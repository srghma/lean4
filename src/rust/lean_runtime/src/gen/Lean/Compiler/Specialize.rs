// Lean compiler output
// Module: Lean.Compiler.Specialize
// Imports: Lean.Meta.Basic Init.Omega
use crate::r#gen::Init::Data::Array::Basic::l_Array_instInhabited;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNatLit_x3f;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getId, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Attributes::{
    l_Lean_ParametricAttribute_getParam_x3f___redArg, l_Lean_TagAttribute_hasTag,
    l_Lean_registerParametricAttribute___redArg, l_Lean_registerTagAttribute,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_type;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::l_Lean_Expr_fvarId_x21;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp,
    l_Lean_FVarId_getUserName___redArg, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_fswap, lean_array_size, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_mk_ref, lean_st_ref_get};
pub static mut l_Lean_Compiler_instInhabitedSpecializeAttributeKind_default: u8 = 0;
pub static mut l_Lean_Compiler_instInhabitedSpecializeAttributeKind: u8 = 0;
pub static l_Lean_Compiler_instBEqSpecializeAttributeKind___closed__0_value:
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
    m_fun: l_Lean_Compiler_instBEqSpecializeAttributeKind_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_instBEqSpecializeAttributeKind___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_instBEqSpecializeAttributeKind___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_instBEqSpecializeAttributeKind: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_instBEqSpecializeAttributeKind___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [110, 111, 115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 0]};
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9741449957638678221 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [109, 97, 114, 107, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 116, 111, 32, 110, 101, 118, 101, 114, 32, 98, 101, 32, 115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 100, 0]};
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [110, 111, 115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8543197020067251012 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16754692123863300632 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_nospecializeAttr: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1___closed__0_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [77, 97, 114, 107, 115, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 116, 111, 32, 110, 101, 118, 101, 114, 32, 98, 101, 32, 115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 100, 32, 100, 117, 114, 105, 110, 103, 32, 99, 111, 100, 101, 32, 103, 101, 110, 101, 114, 97, 116, 105, 111, 110, 46, 10, 0]};
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 20 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 25 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 78 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 78 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 24 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 24 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 35 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 35 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 101, 97, 107, 95, 115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 0]};
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14738992980993031875 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<120> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 120, m_capacity: 120, m_length: 119, m_data: [109, 97, 114, 107, 32, 116, 121, 112, 101, 32, 102, 111, 114, 32, 119, 101, 97, 107, 32, 115, 112, 101, 99, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 58, 32, 105, 110, 115, 116, 97, 110, 99, 101, 115, 32, 97, 114, 101, 32, 111, 110, 108, 121, 32, 115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 100, 32, 119, 104, 101, 110, 32, 97, 110, 111, 116, 104, 101, 114, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 97, 108, 114, 101, 97, 100, 121, 32, 116, 114, 105, 103, 103, 101, 114, 115, 32, 115, 112, 101, 99, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [119, 101, 97, 107, 83, 112, 101, 99, 105, 97, 108, 105, 122, 101, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8543197020067251012 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,6123501543470500011 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_weakSpecializeAttr: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_docString__1___closed__0_value: crate::leanh::LeanStringObject<300> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 300, m_capacity: 300, m_length: 299, m_data: [77, 97, 114, 107, 115, 32, 97, 32, 116, 121, 112, 101, 32, 102, 111, 114, 32, 119, 101, 97, 107, 32, 115, 112, 101, 99, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 58, 32, 80, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 111, 102, 32, 116, 104, 105, 115, 32, 116, 121, 112, 101, 32, 97, 114, 101, 32, 111, 110, 108, 121, 32, 115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 100, 32, 119, 104, 101, 110, 10, 97, 110, 111, 116, 104, 101, 114, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 97, 108, 114, 101, 97, 100, 121, 32, 116, 114, 105, 103, 103, 101, 114, 115, 32, 115, 112, 101, 99, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 46, 32, 85, 110, 108, 105, 107, 101, 32, 96, 64, 91, 110, 111, 115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 93, 96, 44, 32, 105, 102, 32, 115, 112, 101, 99, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 10, 104, 97, 112, 112, 101, 110, 115, 32, 102, 111, 114, 32, 111, 116, 104, 101, 114, 32, 114, 101, 97, 115, 111, 110, 115, 44, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 111, 102, 32, 116, 104, 105, 115, 32, 116, 121, 112, 101, 32, 119, 105, 108, 108, 32, 112, 97, 114, 116, 105, 99, 105, 112, 97, 116, 101, 32, 105, 110, 32, 116, 104, 101, 32, 115, 112, 101, 99, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 10, 114, 97, 116, 104, 101, 114, 32, 116, 104, 97, 110, 32, 98, 101, 105, 110, 103, 32, 105, 103, 110, 111, 114, 101, 100, 46, 10, 0]};
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_docString__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_docString__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 27 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 36 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 125 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 125 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 34 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 34 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 37 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 37 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__0_value: crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 115, 112, 101, 99, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 105, 110, 100, 101, 120, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__2_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [96, 58, 32, 84, 104, 101, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 97, 116, 32, 116, 104, 105, 115, 32, 105, 110, 100, 101, 120, 32, 40, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__4_value: crate::leanh::LeanStringObject<60> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 60, m_capacity: 60, m_length: 59, m_data: [96, 41, 32, 104, 97, 115, 32, 97, 108, 114, 101, 97, 100, 121, 32, 98, 101, 101, 110, 32, 115, 112, 101, 99, 105, 102, 105, 101, 100, 32, 97, 115, 32, 97, 32, 115, 112, 101, 99, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 32, 99, 97, 110, 100, 105, 100, 97, 116, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__6_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 105, 110, 100, 101, 120, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__8_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [96, 58, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__10_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [96, 32, 104, 97, 115, 32, 111, 110, 108, 121, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__12_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__14_value: crate::leanh::LeanStringObject<72> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 72, m_capacity: 72, m_length: 71, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 115, 112, 101, 99, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 105, 110, 100, 101, 120, 32, 96, 48, 96, 58, 32, 73, 110, 100, 101, 120, 32, 109, 117, 115, 116, 32, 98, 101, 32, 103, 114, 101, 97, 116, 101, 114, 32, 116, 104, 97, 110, 32, 48, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__16_value: crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 115, 112, 101, 99, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 110, 97, 109, 101, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__18_value: crate::leanh::LeanStringObject<63> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 63, m_capacity: 63, m_length: 62, m_data: [96, 58, 32, 73, 116, 32, 104, 97, 115, 32, 97, 108, 114, 101, 97, 100, 121, 32, 98, 101, 101, 110, 32, 115, 112, 101, 99, 105, 102, 105, 101, 100, 32, 97, 115, 32, 97, 32, 115, 112, 101, 99, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 32, 99, 97, 110, 100, 105, 100, 97, 116, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__20_value: crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [96, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 104, 97, 118, 101, 32, 97, 110, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 119, 105, 116, 104, 32, 116, 104, 105, 115, 32, 110, 97, 109, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__20_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__21_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__21: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__6_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__8_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__10_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__12_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__14_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__16_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__18_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0 + 24) as u16, other: 0, tag: 0 }, m_objs: [282574488338432 as *mut crate::leanh::LeanObject,72621647814721793 as *mut crate::leanh::LeanObject,65793 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_: u64 = 0;
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__9_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__9_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8543197020067251012 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5478851864234427460 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 0]};
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17651876509044871153 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [109, 97, 114, 107, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 116, 111, 32, 97, 108, 119, 97, 121, 115, 32, 98, 101, 32, 115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 100, 0]};
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,0 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 8) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,0 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_specializeAttr: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1___closed__0_value: crate::leanh::LeanStringObject<750> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 750, m_capacity: 750, m_length: 749, m_data: [77, 97, 114, 107, 115, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 116, 111, 32, 97, 108, 119, 97, 121, 115, 32, 98, 101, 32, 115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 100, 32, 100, 117, 114, 105, 110, 103, 32, 99, 111, 100, 101, 32, 103, 101, 110, 101, 114, 97, 116, 105, 111, 110, 46, 10, 10, 83, 112, 101, 99, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 32, 105, 115, 32, 97, 110, 32, 111, 112, 116, 105, 109, 105, 122, 97, 116, 105, 111, 110, 32, 105, 110, 32, 116, 104, 101, 32, 99, 111, 100, 101, 32, 103, 101, 110, 101, 114, 97, 116, 111, 114, 32, 102, 111, 114, 32, 103, 101, 110, 101, 114, 97, 116, 105, 110, 103, 32, 118, 97, 114, 105, 97, 110, 116, 115, 32, 111, 102, 32, 97, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 116, 104, 97, 116, 10, 97, 114, 101, 32, 115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 100, 32, 116, 111, 32, 115, 112, 101, 99, 105, 102, 105, 99, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 118, 97, 108, 117, 101, 115, 46, 32, 84, 104, 105, 115, 32, 105, 115, 32, 105, 110, 32, 112, 97, 114, 116, 105, 99, 117, 108, 97, 114, 32, 117, 115, 101, 102, 117, 108, 32, 102, 111, 114, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 32, 116, 104, 97, 116, 32, 116, 97, 107, 101, 10, 111, 116, 104, 101, 114, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 32, 97, 115, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 58, 32, 85, 115, 117, 97, 108, 108, 121, 32, 119, 104, 101, 110, 32, 112, 97, 115, 115, 105, 110, 103, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 32, 97, 115, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 44, 32, 97, 32, 99, 108, 111, 115, 117, 114, 101, 32, 110, 101, 101, 100, 115, 32, 116, 111, 32, 98, 101, 10, 97, 108, 108, 111, 99, 97, 116, 101, 100, 32, 116, 104, 97, 116, 32, 119, 105, 108, 108, 32, 116, 104, 101, 110, 32, 98, 101, 32, 99, 97, 108, 108, 101, 100, 46, 32, 85, 115, 105, 110, 103, 32, 96, 64, 91, 115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 93, 96, 32, 112, 114, 101, 118, 101, 110, 116, 115, 32, 98, 111, 116, 104, 32, 111, 102, 32, 116, 104, 101, 115, 101, 32, 111, 112, 101, 114, 97, 116, 105, 111, 110, 115, 32, 98, 121, 10, 117, 115, 105, 110, 103, 32, 116, 104, 101, 32, 112, 114, 111, 118, 105, 100, 101, 100, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 100, 105, 114, 101, 99, 116, 108, 121, 32, 105, 110, 32, 116, 104, 101, 32, 115, 112, 101, 99, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 32, 111, 102, 32, 116, 104, 101, 32, 105, 110, 110, 101, 114, 32, 102, 117, 110, 99, 116, 105, 111, 110, 46, 10, 10, 96, 64, 91, 115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 93, 96, 32, 99, 97, 110, 32, 116, 97, 107, 101, 32, 97, 100, 100, 105, 116, 105, 111, 110, 97, 108, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 32, 102, 111, 114, 32, 116, 104, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 110, 97, 109, 101, 115, 32, 111, 114, 32, 105, 110, 100, 105, 99, 101, 115, 32, 40, 115, 116, 97, 114, 116, 105, 110, 103, 32, 97, 116, 32, 49, 41, 32, 111, 102, 10, 116, 104, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 116, 104, 97, 116, 32, 115, 104, 111, 117, 108, 100, 32, 98, 101, 32, 115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 100, 46, 32, 66, 121, 32, 100, 101, 102, 97, 117, 108, 116, 44, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 97, 110, 100, 32, 102, 117, 110, 99, 116, 105, 111, 110, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 97, 114, 101, 10, 115, 112, 101, 99, 105, 97, 108, 105, 122, 101, 100, 46, 10, 0]};
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 64 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 85 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 3 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 3 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 78 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 78 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 33 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 33 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_getSpecializationArgs_x3f___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_getSpecializationArgs_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Compiler_SpecializeAttributeKind_ctorIdx(
    mut v_x_1389_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_x_1389_ == 0 {
        let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1390_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_1390_;
    } else {
        let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1391_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_1391_;
    }
}
pub unsafe fn l_Lean_Compiler_SpecializeAttributeKind_ctorIdx___boxed(
    mut v_x_1392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_1393_: u8 = 0;
    let mut v_res_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1393_ = (crate::leanh::lean_unbox(v_x_1392_) as u8);
    v_res_1394_ = l_Lean_Compiler_SpecializeAttributeKind_ctorIdx(v_x_boxed_1393_);
    return v_res_1394_;
}
pub unsafe fn l_Lean_Compiler_SpecializeAttributeKind_toCtorIdx(
    mut v_x_1395_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1396_ = l_Lean_Compiler_SpecializeAttributeKind_ctorIdx(v_x_1395_);
    return v___x_1396_;
}
pub unsafe fn l_Lean_Compiler_SpecializeAttributeKind_toCtorIdx___boxed(
    mut v_x_1397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_1398_: u8 = 0;
    let mut v_res_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1398_ = (crate::leanh::lean_unbox(v_x_1397_) as u8);
    v_res_1399_ = l_Lean_Compiler_SpecializeAttributeKind_toCtorIdx(v_x_4__boxed_1398_);
    return v_res_1399_;
}
pub unsafe fn l_Lean_Compiler_SpecializeAttributeKind_ctorElim___redArg(
    mut v_k_1400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1400_);
    return v_k_1400_;
}
pub unsafe fn l_Lean_Compiler_SpecializeAttributeKind_ctorElim___redArg___boxed(
    mut v_k_1401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1402_ = l_Lean_Compiler_SpecializeAttributeKind_ctorElim___redArg(v_k_1401_);
    crate::leanh::lean_dec(v_k_1401_);
    return v_res_1402_;
}
pub unsafe fn l_Lean_Compiler_SpecializeAttributeKind_ctorElim(
    mut v_motive_1403_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1404_: *mut crate::leanh::LeanObject,
    mut v_t_1405_: u8,
    mut v_h_1406_: *mut crate::leanh::LeanObject,
    mut v_k_1407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1407_);
    return v_k_1407_;
}
pub unsafe fn l_Lean_Compiler_SpecializeAttributeKind_ctorElim___boxed(
    mut v_motive_1408_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1409_: *mut crate::leanh::LeanObject,
    mut v_t_1410_: *mut crate::leanh::LeanObject,
    mut v_h_1411_: *mut crate::leanh::LeanObject,
    mut v_k_1412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1413_: u8 = 0;
    let mut v_res_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1413_ = (crate::leanh::lean_unbox(v_t_1410_) as u8);
    v_res_1414_ = l_Lean_Compiler_SpecializeAttributeKind_ctorElim(
        v_motive_1408_,
        v_ctorIdx_1409_,
        v_t_boxed_1413_,
        v_h_1411_,
        v_k_1412_,
    );
    crate::leanh::lean_dec(v_k_1412_);
    crate::leanh::lean_dec(v_ctorIdx_1409_);
    return v_res_1414_;
}
pub unsafe fn l_Lean_Compiler_SpecializeAttributeKind_specialize_elim___redArg(
    mut v_specialize_1415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_specialize_1415_);
    return v_specialize_1415_;
}
pub unsafe fn l_Lean_Compiler_SpecializeAttributeKind_specialize_elim___redArg___boxed(
    mut v_specialize_1416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1417_ =
        l_Lean_Compiler_SpecializeAttributeKind_specialize_elim___redArg(v_specialize_1416_);
    crate::leanh::lean_dec(v_specialize_1416_);
    return v_res_1417_;
}
pub unsafe fn l_Lean_Compiler_SpecializeAttributeKind_specialize_elim(
    mut v_motive_1418_: *mut crate::leanh::LeanObject,
    mut v_t_1419_: u8,
    mut v_h_1420_: *mut crate::leanh::LeanObject,
    mut v_specialize_1421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_specialize_1421_);
    return v_specialize_1421_;
}
pub unsafe fn l_Lean_Compiler_SpecializeAttributeKind_specialize_elim___boxed(
    mut v_motive_1422_: *mut crate::leanh::LeanObject,
    mut v_t_1423_: *mut crate::leanh::LeanObject,
    mut v_h_1424_: *mut crate::leanh::LeanObject,
    mut v_specialize_1425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1426_: u8 = 0;
    let mut v_res_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1426_ = (crate::leanh::lean_unbox(v_t_1423_) as u8);
    v_res_1427_ = l_Lean_Compiler_SpecializeAttributeKind_specialize_elim(
        v_motive_1422_,
        v_t_boxed_1426_,
        v_h_1424_,
        v_specialize_1425_,
    );
    crate::leanh::lean_dec(v_specialize_1425_);
    return v_res_1427_;
}
pub unsafe fn l_Lean_Compiler_SpecializeAttributeKind_nospecialize_elim___redArg(
    mut v_nospecialize_1428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_nospecialize_1428_);
    return v_nospecialize_1428_;
}
pub unsafe fn l_Lean_Compiler_SpecializeAttributeKind_nospecialize_elim___redArg___boxed(
    mut v_nospecialize_1429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1430_ =
        l_Lean_Compiler_SpecializeAttributeKind_nospecialize_elim___redArg(v_nospecialize_1429_);
    crate::leanh::lean_dec(v_nospecialize_1429_);
    return v_res_1430_;
}
pub unsafe fn l_Lean_Compiler_SpecializeAttributeKind_nospecialize_elim(
    mut v_motive_1431_: *mut crate::leanh::LeanObject,
    mut v_t_1432_: u8,
    mut v_h_1433_: *mut crate::leanh::LeanObject,
    mut v_nospecialize_1434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_nospecialize_1434_);
    return v_nospecialize_1434_;
}
pub unsafe fn l_Lean_Compiler_SpecializeAttributeKind_nospecialize_elim___boxed(
    mut v_motive_1435_: *mut crate::leanh::LeanObject,
    mut v_t_1436_: *mut crate::leanh::LeanObject,
    mut v_h_1437_: *mut crate::leanh::LeanObject,
    mut v_nospecialize_1438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1439_: u8 = 0;
    let mut v_res_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1439_ = (crate::leanh::lean_unbox(v_t_1436_) as u8);
    v_res_1440_ = l_Lean_Compiler_SpecializeAttributeKind_nospecialize_elim(
        v_motive_1435_,
        v_t_boxed_1439_,
        v_h_1437_,
        v_nospecialize_1438_,
    );
    crate::leanh::lean_dec(v_nospecialize_1438_);
    return v_res_1440_;
}
pub unsafe fn _init_l_Lean_Compiler_instInhabitedSpecializeAttributeKind_default() -> u8 {
    let mut v___x_1441_: u8 = 0;
    v___x_1441_ = 0;
    return v___x_1441_;
}
pub unsafe fn _init_l_Lean_Compiler_instInhabitedSpecializeAttributeKind() -> u8 {
    let mut v___x_1442_: u8 = 0;
    v___x_1442_ = 0;
    return v___x_1442_;
}
pub unsafe fn l_Lean_Compiler_instBEqSpecializeAttributeKind_beq(
    mut v_x_1443_: u8,
    mut v_y_1444_: u8,
) -> u8 {
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: u8 = 0;
    v___x_1445_ = l_Lean_Compiler_SpecializeAttributeKind_ctorIdx(v_x_1443_);
    v___x_1446_ = l_Lean_Compiler_SpecializeAttributeKind_ctorIdx(v_y_1444_);
    v___x_1447_ = lean_nat_dec_eq(v___x_1445_, v___x_1446_);
    crate::leanh::lean_dec(v___x_1446_);
    crate::leanh::lean_dec(v___x_1445_);
    return v___x_1447_;
}
pub unsafe fn l_Lean_Compiler_instBEqSpecializeAttributeKind_beq___boxed(
    mut v_x_1448_: *mut crate::leanh::LeanObject,
    mut v_y_1449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_17__boxed_1450_: u8 = 0;
    let mut v_y_18__boxed_1451_: u8 = 0;
    let mut v_res_1452_: u8 = 0;
    let mut v_r_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_1450_ = (crate::leanh::lean_unbox(v_x_1448_) as u8);
    v_y_18__boxed_1451_ = (crate::leanh::lean_unbox(v_y_1449_) as u8);
    v_res_1452_ = l_Lean_Compiler_instBEqSpecializeAttributeKind_beq(
        v_x_17__boxed_1450_,
        v_y_18__boxed_1451_,
    );
    v_r_1453_ = crate::leanh::lean_box((v_res_1452_) as usize);
    return v_r_1453_;
}
pub unsafe fn l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_(
    mut v_x_1456_: *mut crate::leanh::LeanObject,
    mut v___y_1457_: *mut crate::leanh::LeanObject,
    mut v___y_1458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1460_ = crate::leanh::lean_box(0);
    v___x_1461_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1461_, 0, v___x_1460_);
    return v___x_1461_;
}
pub unsafe fn l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2____boxed(
    mut v_x_1462_: *mut crate::leanh::LeanObject,
    mut v___y_1463_: *mut crate::leanh::LeanObject,
    mut v___y_1464_: *mut crate::leanh::LeanObject,
    mut v___y_1465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1466_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_(v_x_1462_, v___y_1463_, v___y_1464_);
    crate::leanh::lean_dec(v___y_1464_);
    crate::leanh::lean_dec_ref(v___y_1463_);
    crate::leanh::lean_dec(v_x_1462_);
    return v_res_1466_;
}
pub unsafe fn l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: u8 = 0;
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1480_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_;
    v___x_1481_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_;
    v___x_1482_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_;
    v___x_1483_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_;
    v___x_1484_ = 0;
    v___x_1485_ = crate::leanh::lean_box(2);
    v___x_1486_ = l_Lean_registerTagAttribute(
        v___x_1481_,
        v___x_1482_,
        v___f_1480_,
        v___x_1483_,
        v___x_1484_,
        v___x_1485_,
    );
    return v___x_1486_;
}
pub unsafe fn l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2____boxed(
    mut v_a_1487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1488_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_();
    return v_res_1488_;
}
pub unsafe fn l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1491_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_;
    v___x_1492_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1___closed__0;
    v___x_1493_ = l_Lean_addBuiltinDocString(v___x_1491_, v___x_1492_);
    return v___x_1493_;
}
pub unsafe fn l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1___boxed(
    mut v_a_1494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1495_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1();
    return v_res_1495_;
}
pub unsafe fn l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1522_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_;
    v___x_1523_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___closed__6;
    v___x_1524_ = l_Lean_addBuiltinDeclarationRanges(v___x_1522_, v___x_1523_);
    return v___x_1524_;
}
pub unsafe fn l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3___boxed(
    mut v_a_1525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1526_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3();
    return v_res_1526_;
}
pub unsafe fn l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: u8 = 0;
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1537_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_;
    v___x_1538_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_;
    v___x_1539_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_;
    v___x_1540_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_;
    v___x_1541_ = 0;
    v___x_1542_ = crate::leanh::lean_box(2);
    v___x_1543_ = l_Lean_registerTagAttribute(
        v___x_1538_,
        v___x_1539_,
        v___f_1537_,
        v___x_1540_,
        v___x_1541_,
        v___x_1542_,
    );
    return v___x_1543_;
}
pub unsafe fn l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2____boxed(
    mut v_a_1544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1545_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_();
    return v_res_1545_;
}
pub unsafe fn l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_docString__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1548_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_;
    v___x_1549_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_docString__1___closed__0;
    v___x_1550_ = l_Lean_addBuiltinDocString(v___x_1548_, v___x_1549_);
    return v___x_1550_;
}
pub unsafe fn l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_docString__1___boxed(
    mut v_a_1551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1552_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_docString__1();
    return v_res_1552_;
}
pub unsafe fn l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1579_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_;
    v___x_1580_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___closed__6;
    v___x_1581_ = l_Lean_addBuiltinDeclarationRanges(v___x_1579_, v___x_1580_);
    return v___x_1581_;
}
pub unsafe fn l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3___boxed(
    mut v_a_1582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1583_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3();
    return v_res_1583_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___lam__0(
    mut v_k_1584_: *mut crate::leanh::LeanObject,
    mut v_b_1585_: *mut crate::leanh::LeanObject,
    mut v_c_1586_: *mut crate::leanh::LeanObject,
    mut v___y_1587_: *mut crate::leanh::LeanObject,
    mut v___y_1588_: *mut crate::leanh::LeanObject,
    mut v___y_1589_: *mut crate::leanh::LeanObject,
    mut v___y_1590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1590_);
    crate::leanh::lean_inc_ref(v___y_1589_);
    crate::leanh::lean_inc(v___y_1588_);
    crate::leanh::lean_inc_ref(v___y_1587_);
    v___x_1592_ = crate::leanh::lean_apply_7(
        v_k_1584_,
        v_b_1585_,
        v_c_1586_,
        v___y_1587_,
        v___y_1588_,
        v___y_1589_,
        v___y_1590_,
        crate::leanh::lean_box(0),
    );
    return v___x_1592_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___lam__0___boxed(
    mut v_k_1593_: *mut crate::leanh::LeanObject,
    mut v_b_1594_: *mut crate::leanh::LeanObject,
    mut v_c_1595_: *mut crate::leanh::LeanObject,
    mut v___y_1596_: *mut crate::leanh::LeanObject,
    mut v___y_1597_: *mut crate::leanh::LeanObject,
    mut v___y_1598_: *mut crate::leanh::LeanObject,
    mut v___y_1599_: *mut crate::leanh::LeanObject,
    mut v___y_1600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1601_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___lam__0(v_k_1593_, v_b_1594_, v_c_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
    crate::leanh::lean_dec(v___y_1599_);
    crate::leanh::lean_dec_ref(v___y_1598_);
    crate::leanh::lean_dec(v___y_1597_);
    crate::leanh::lean_dec_ref(v___y_1596_);
    return v_res_1601_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg(
    mut v_type_1602_: *mut crate::leanh::LeanObject,
    mut v_k_1603_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1604_: u8,
    mut v_whnfType_1605_: u8,
    mut v___y_1606_: *mut crate::leanh::LeanObject,
    mut v___y_1607_: *mut crate::leanh::LeanObject,
    mut v___y_1608_: *mut crate::leanh::LeanObject,
    mut v___y_1609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1616_: u8 = 0;
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1620_: u8 = 0;
    let mut v_a_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1624_: u8 = 0;
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1628_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1611_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_1611_, 0, v_k_1603_);
                v___x_1612_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    crate::leanh::lean_box(0),
                    v_type_1602_,
                    v___f_1611_,
                    v_cleanupAnnotations_1604_,
                    v_whnfType_1605_,
                    v___y_1606_,
                    v___y_1607_,
                    v___y_1608_,
                    v___y_1609_,
                );
                if crate::leanh::lean_obj_tag(v___x_1612_) == 0 {
                    v_a_1613_ = crate::leanh::lean_ctor_get(v___x_1612_, 0);
                    v_isSharedCheck_1620_ = (!crate::leanh::lean_is_exclusive(v___x_1612_)) as u8;
                    if v_isSharedCheck_1620_ == 0 {
                        v___x_1615_ = v___x_1612_;
                        v_isShared_1616_ = v_isSharedCheck_1620_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1613_);
                        crate::leanh::lean_dec(v___x_1612_);
                        v___x_1615_ = crate::leanh::lean_box(0);
                        v_isShared_1616_ = v_isSharedCheck_1620_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1621_ = crate::leanh::lean_ctor_get(v___x_1612_, 0);
                    v_isSharedCheck_1628_ = (!crate::leanh::lean_is_exclusive(v___x_1612_)) as u8;
                    if v_isSharedCheck_1628_ == 0 {
                        v___x_1623_ = v___x_1612_;
                        v_isShared_1624_ = v_isSharedCheck_1628_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1621_);
                        crate::leanh::lean_dec(v___x_1612_);
                        v___x_1623_ = crate::leanh::lean_box(0);
                        v_isShared_1624_ = v_isSharedCheck_1628_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1616_ == 0 {
                    v___x_1618_ = v___x_1615_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1619_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
                    v___x_1618_ = v_reuseFailAlloc_1619_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1618_;
            }
            3 => {
                if v_isShared_1624_ == 0 {
                    v___x_1626_ = v___x_1623_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1627_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
                    v___x_1626_ = v_reuseFailAlloc_1627_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1626_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg___boxed(
    mut v_type_1629_: *mut crate::leanh::LeanObject,
    mut v_k_1630_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1631_: *mut crate::leanh::LeanObject,
    mut v_whnfType_1632_: *mut crate::leanh::LeanObject,
    mut v___y_1633_: *mut crate::leanh::LeanObject,
    mut v___y_1634_: *mut crate::leanh::LeanObject,
    mut v___y_1635_: *mut crate::leanh::LeanObject,
    mut v___y_1636_: *mut crate::leanh::LeanObject,
    mut v___y_1637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1638_: u8 = 0;
    let mut v_whnfType_boxed_1639_: u8 = 0;
    let mut v_res_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1638_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1631_) as u8);
    v_whnfType_boxed_1639_ = (crate::leanh::lean_unbox(v_whnfType_1632_) as u8);
    v_res_1640_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg(v_type_1629_, v_k_1630_, v_cleanupAnnotations_boxed_1638_, v_whnfType_boxed_1639_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
    crate::leanh::lean_dec(v___y_1636_);
    crate::leanh::lean_dec_ref(v___y_1635_);
    crate::leanh::lean_dec(v___y_1634_);
    crate::leanh::lean_dec_ref(v___y_1633_);
    return v_res_1640_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7(
    mut v_00_u03b1_1641_: *mut crate::leanh::LeanObject,
    mut v_type_1642_: *mut crate::leanh::LeanObject,
    mut v_k_1643_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1644_: u8,
    mut v_whnfType_1645_: u8,
    mut v___y_1646_: *mut crate::leanh::LeanObject,
    mut v___y_1647_: *mut crate::leanh::LeanObject,
    mut v___y_1648_: *mut crate::leanh::LeanObject,
    mut v___y_1649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1651_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg(v_type_1642_, v_k_1643_, v_cleanupAnnotations_1644_, v_whnfType_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
    return v___x_1651_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___boxed(
    mut v_00_u03b1_1652_: *mut crate::leanh::LeanObject,
    mut v_type_1653_: *mut crate::leanh::LeanObject,
    mut v_k_1654_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1655_: *mut crate::leanh::LeanObject,
    mut v_whnfType_1656_: *mut crate::leanh::LeanObject,
    mut v___y_1657_: *mut crate::leanh::LeanObject,
    mut v___y_1658_: *mut crate::leanh::LeanObject,
    mut v___y_1659_: *mut crate::leanh::LeanObject,
    mut v___y_1660_: *mut crate::leanh::LeanObject,
    mut v___y_1661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1662_: u8 = 0;
    let mut v_whnfType_boxed_1663_: u8 = 0;
    let mut v_res_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1662_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1655_) as u8);
    v_whnfType_boxed_1663_ = (crate::leanh::lean_unbox(v_whnfType_1656_) as u8);
    v_res_1664_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7(v_00_u03b1_1652_, v_type_1653_, v_k_1654_, v_cleanupAnnotations_boxed_1662_, v_whnfType_boxed_1663_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
    crate::leanh::lean_dec(v___y_1660_);
    crate::leanh::lean_dec_ref(v___y_1659_);
    crate::leanh::lean_dec(v___y_1658_);
    crate::leanh::lean_dec_ref(v___y_1657_);
    return v_res_1664_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8___redArg(
    mut v_hi_1665_: *mut crate::leanh::LeanObject,
    mut v_pivot_1666_: *mut crate::leanh::LeanObject,
    mut v_as_1667_: *mut crate::leanh::LeanObject,
    mut v_i_1668_: *mut crate::leanh::LeanObject,
    mut v_k_1669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1670_: u8 = 0;
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: u8 = 0;
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1670_ = lean_nat_dec_lt(v_k_1669_, v_hi_1665_);
                if v___x_1670_ == 0 {
                    crate::leanh::lean_dec(v_k_1669_);
                    v___x_1671_ = lean_array_fswap(v_as_1667_, v_i_1668_, v_hi_1665_);
                    v___x_1672_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1672_, 0, v_i_1668_);
                    crate::leanh::lean_ctor_set(v___x_1672_, 1, v___x_1671_);
                    return v___x_1672_;
                } else {
                    v___x_1673_ = lean_array_fget_borrowed(v_as_1667_, v_k_1669_);
                    v___x_1674_ = lean_nat_dec_lt(v___x_1673_, v_pivot_1666_);
                    if v___x_1674_ == 0 {
                        v___x_1675_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1676_ = lean_nat_add(v_k_1669_, v___x_1675_);
                        crate::leanh::lean_dec(v_k_1669_);
                        v_k_1669_ = v___x_1676_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1678_ = lean_array_fswap(v_as_1667_, v_i_1668_, v_k_1669_);
                        v___x_1679_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1680_ = lean_nat_add(v_i_1668_, v___x_1679_);
                        crate::leanh::lean_dec(v_i_1668_);
                        v___x_1681_ = lean_nat_add(v_k_1669_, v___x_1679_);
                        crate::leanh::lean_dec(v_k_1669_);
                        v_as_1667_ = v___x_1678_;
                        v_i_1668_ = v___x_1680_;
                        v_k_1669_ = v___x_1681_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8___redArg___boxed(
    mut v_hi_1683_: *mut crate::leanh::LeanObject,
    mut v_pivot_1684_: *mut crate::leanh::LeanObject,
    mut v_as_1685_: *mut crate::leanh::LeanObject,
    mut v_i_1686_: *mut crate::leanh::LeanObject,
    mut v_k_1687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1688_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8___redArg(v_hi_1683_, v_pivot_1684_, v_as_1685_, v_i_1686_, v_k_1687_);
    crate::leanh::lean_dec(v_pivot_1684_);
    crate::leanh::lean_dec(v_hi_1683_);
    return v_res_1688_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg(
    mut v_n_1689_: *mut crate::leanh::LeanObject,
    mut v_as_1690_: *mut crate::leanh::LeanObject,
    mut v_lo_1691_: *mut crate::leanh::LeanObject,
    mut v_hi_1692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: u8 = 0;
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: u8 = 0;
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: u8 = 0;
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: u8 = 0;
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: u8 = 0;
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1704_ = lean_nat_dec_lt(v_lo_1691_, v_hi_1692_);
                if v___x_1704_ == 0 {
                    crate::leanh::lean_dec(v_lo_1691_);
                    return v_as_1690_;
                } else {
                    v___x_1705_ = lean_nat_add(v_lo_1691_, v_hi_1692_);
                    v___x_1706_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_1707_ = lean_nat_shiftr(v___x_1705_, v___x_1706_);
                    crate::leanh::lean_dec(v___x_1705_);
                    v___x_1720_ = lean_array_fget_borrowed(v_as_1690_, v_mid_1707_);
                    v___x_1721_ = lean_array_fget_borrowed(v_as_1690_, v_lo_1691_);
                    v___x_1722_ = lean_nat_dec_lt(v___x_1720_, v___x_1721_);
                    if v___x_1722_ == 0 {
                        v___y_1715_ = v_as_1690_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1723_ = lean_array_fswap(v_as_1690_, v_lo_1691_, v_mid_1707_);
                        v___y_1715_ = v___x_1723_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_1695_ = lean_array_fget(v___y_1694_, v_hi_1692_);
                crate::leanh::lean_inc_n(v_lo_1691_, 2);
                v___x_1696_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8___redArg(v_hi_1692_, v_pivot_1695_, v___y_1694_, v_lo_1691_, v_lo_1691_);
                crate::leanh::lean_dec(v_pivot_1695_);
                v_fst_1697_ = crate::leanh::lean_ctor_get(v___x_1696_, 0);
                crate::leanh::lean_inc(v_fst_1697_);
                v_snd_1698_ = crate::leanh::lean_ctor_get(v___x_1696_, 1);
                crate::leanh::lean_inc(v_snd_1698_);
                crate::leanh::lean_dec_ref(v___x_1696_);
                v___x_1699_ = lean_nat_dec_le(v_hi_1692_, v_fst_1697_);
                if v___x_1699_ == 0 {
                    v___x_1700_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg(v_n_1689_, v_snd_1698_, v_lo_1691_, v_fst_1697_);
                    v___x_1701_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1702_ = lean_nat_add(v_fst_1697_, v___x_1701_);
                    crate::leanh::lean_dec(v_fst_1697_);
                    v_as_1690_ = v___x_1700_;
                    v_lo_1691_ = v___x_1702_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_1697_);
                    crate::leanh::lean_dec(v_lo_1691_);
                    return v_snd_1698_;
                }
            }
            2 => {
                v___x_1710_ = lean_array_fget_borrowed(v___y_1709_, v_mid_1707_);
                v___x_1711_ = lean_array_fget_borrowed(v___y_1709_, v_hi_1692_);
                v___x_1712_ = lean_nat_dec_lt(v___x_1710_, v___x_1711_);
                if v___x_1712_ == 0 {
                    crate::leanh::lean_dec(v_mid_1707_);
                    v___y_1694_ = v___y_1709_;
                    state = 1;
                    continue;
                } else {
                    v___x_1713_ = lean_array_fswap(v___y_1709_, v_mid_1707_, v_hi_1692_);
                    crate::leanh::lean_dec(v_mid_1707_);
                    v___y_1694_ = v___x_1713_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1716_ = lean_array_fget_borrowed(v___y_1715_, v_hi_1692_);
                v___x_1717_ = lean_array_fget_borrowed(v___y_1715_, v_lo_1691_);
                v___x_1718_ = lean_nat_dec_lt(v___x_1716_, v___x_1717_);
                if v___x_1718_ == 0 {
                    v___y_1709_ = v___y_1715_;
                    state = 2;
                    continue;
                } else {
                    v___x_1719_ = lean_array_fswap(v___y_1715_, v_lo_1691_, v_hi_1692_);
                    v___y_1709_ = v___x_1719_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg___boxed(
    mut v_n_1724_: *mut crate::leanh::LeanObject,
    mut v_as_1725_: *mut crate::leanh::LeanObject,
    mut v_lo_1726_: *mut crate::leanh::LeanObject,
    mut v_hi_1727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1728_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg(v_n_1724_, v_as_1725_, v_lo_1726_, v_hi_1727_);
    crate::leanh::lean_dec(v_hi_1727_);
    crate::leanh::lean_dec(v_n_1724_);
    return v_res_1728_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___redArg(
    mut v_sz_1729_: usize,
    mut v_i_1730_: usize,
    mut v_bs_1731_: *mut crate::leanh::LeanObject,
    mut v___y_1732_: *mut crate::leanh::LeanObject,
    mut v___y_1733_: *mut crate::leanh::LeanObject,
    mut v___y_1734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1736_: u8 = 0;
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: usize = 0;
    let mut v___x_1745_: usize = 0;
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1751_: u8 = 0;
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1755_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1736_ = lean_usize_dec_lt(v_i_1730_, v_sz_1729_);
                if v___x_1736_ == 0 {
                    v___x_1737_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1737_, 0, v_bs_1731_);
                    return v___x_1737_;
                } else {
                    v_v_1738_ = lean_array_uget_borrowed(v_bs_1731_, v_i_1730_);
                    v___x_1739_ = l_Lean_Expr_fvarId_x21(v_v_1738_);
                    v___x_1740_ = l_Lean_FVarId_getUserName___redArg(
                        v___x_1739_,
                        v___y_1732_,
                        v___y_1733_,
                        v___y_1734_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1740_) == 0 {
                        v_a_1741_ = crate::leanh::lean_ctor_get(v___x_1740_, 0);
                        crate::leanh::lean_inc(v_a_1741_);
                        crate::leanh::lean_dec_ref_known(v___x_1740_, 1);
                        v___x_1742_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_1743_ = lean_array_uset(v_bs_1731_, v_i_1730_, v___x_1742_);
                        v___x_1744_ = 1usize;
                        v___x_1745_ = lean_usize_add(v_i_1730_, v___x_1744_);
                        v___x_1746_ = lean_array_uset(v_bs_x27_1743_, v_i_1730_, v_a_1741_);
                        v_i_1730_ = v___x_1745_;
                        v_bs_1731_ = v___x_1746_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_1731_);
                        v_a_1748_ = crate::leanh::lean_ctor_get(v___x_1740_, 0);
                        v_isSharedCheck_1755_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1740_)) as u8;
                        if v_isSharedCheck_1755_ == 0 {
                            v___x_1750_ = v___x_1740_;
                            v_isShared_1751_ = v_isSharedCheck_1755_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1748_);
                            crate::leanh::lean_dec(v___x_1740_);
                            v___x_1750_ = crate::leanh::lean_box(0);
                            v_isShared_1751_ = v_isSharedCheck_1755_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1751_ == 0 {
                    v___x_1753_ = v___x_1750_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1754_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
                    v___x_1753_ = v_reuseFailAlloc_1754_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1753_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___redArg___boxed(
    mut v_sz_1756_: *mut crate::leanh::LeanObject,
    mut v_i_1757_: *mut crate::leanh::LeanObject,
    mut v_bs_1758_: *mut crate::leanh::LeanObject,
    mut v___y_1759_: *mut crate::leanh::LeanObject,
    mut v___y_1760_: *mut crate::leanh::LeanObject,
    mut v___y_1761_: *mut crate::leanh::LeanObject,
    mut v___y_1762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1763_: usize = 0;
    let mut v_i_boxed_1764_: usize = 0;
    let mut v_res_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1763_ = crate::leanh::lean_unbox_usize(v_sz_1756_);
    crate::leanh::lean_dec(v_sz_1756_);
    v_i_boxed_1764_ = crate::leanh::lean_unbox_usize(v_i_1757_);
    crate::leanh::lean_dec(v_i_1757_);
    v_res_1765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___redArg(v_sz_boxed_1763_, v_i_boxed_1764_, v_bs_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
    crate::leanh::lean_dec(v___y_1761_);
    crate::leanh::lean_dec_ref(v___y_1760_);
    crate::leanh::lean_dec_ref(v___y_1759_);
    return v_res_1765_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1_spec__1(
    mut v_a_1766_: *mut crate::leanh::LeanObject,
    mut v_as_1767_: *mut crate::leanh::LeanObject,
    mut v_i_1768_: usize,
    mut v_stop_1769_: usize,
) -> u8 {
    let mut v___x_1770_: u8 = 0;
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: u8 = 0;
    let mut v___x_1773_: usize = 0;
    let mut v___x_1774_: usize = 0;
    let mut v___x_1776_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1770_ = lean_usize_dec_eq(v_i_1768_, v_stop_1769_);
                if v___x_1770_ == 0 {
                    v___x_1771_ = lean_array_uget_borrowed(v_as_1767_, v_i_1768_);
                    v___x_1772_ = lean_nat_dec_eq(v_a_1766_, v___x_1771_);
                    if v___x_1772_ == 0 {
                        v___x_1773_ = 1usize;
                        v___x_1774_ = lean_usize_add(v_i_1768_, v___x_1773_);
                        v_i_1768_ = v___x_1774_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1772_;
                    }
                } else {
                    v___x_1776_ = 0;
                    return v___x_1776_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1_spec__1___boxed(
    mut v_a_1777_: *mut crate::leanh::LeanObject,
    mut v_as_1778_: *mut crate::leanh::LeanObject,
    mut v_i_1779_: *mut crate::leanh::LeanObject,
    mut v_stop_1780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1781_: usize = 0;
    let mut v_stop_boxed_1782_: usize = 0;
    let mut v_res_1783_: u8 = 0;
    let mut v_r_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1781_ = crate::leanh::lean_unbox_usize(v_i_1779_);
    crate::leanh::lean_dec(v_i_1779_);
    v_stop_boxed_1782_ = crate::leanh::lean_unbox_usize(v_stop_1780_);
    crate::leanh::lean_dec(v_stop_1780_);
    v_res_1783_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1_spec__1(v_a_1777_, v_as_1778_, v_i_boxed_1781_, v_stop_boxed_1782_);
    crate::leanh::lean_dec_ref(v_as_1778_);
    crate::leanh::lean_dec(v_a_1777_);
    v_r_1784_ = crate::leanh::lean_box((v_res_1783_) as usize);
    return v_r_1784_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1(
    mut v_as_1785_: *mut crate::leanh::LeanObject,
    mut v_a_1786_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: u8 = 0;
    v___x_1787_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1788_ = lean_array_get_size(v_as_1785_);
    v___x_1789_ = lean_nat_dec_lt(v___x_1787_, v___x_1788_);
    if v___x_1789_ == 0 {
        return v___x_1789_;
    } else {
        if v___x_1789_ == 0 {
            return v___x_1789_;
        } else {
            let mut v___x_1790_: usize = 0;
            let mut v___x_1791_: usize = 0;
            let mut v___x_1792_: u8 = 0;
            v___x_1790_ = 0usize;
            v___x_1791_ = lean_usize_of_nat(v___x_1788_);
            v___x_1792_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1_spec__1(v_a_1786_, v_as_1785_, v___x_1790_, v___x_1791_);
            return v___x_1792_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1___boxed(
    mut v_as_1793_: *mut crate::leanh::LeanObject,
    mut v_a_1794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1795_: u8 = 0;
    let mut v_r_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1795_ = l_Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1(v_as_1793_, v_a_1794_);
    crate::leanh::lean_dec(v_a_1794_);
    crate::leanh::lean_dec_ref(v_as_1793_);
    v_r_1796_ = crate::leanh::lean_box((v_res_1795_) as usize);
    return v_r_1796_;
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5_spec__8(
    mut v_xs_1797_: *mut crate::leanh::LeanObject,
    mut v_v_1798_: *mut crate::leanh::LeanObject,
    mut v_i_1799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: u8 = 0;
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: u8 = 0;
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1800_ = lean_array_get_size(v_xs_1797_);
                v___x_1801_ = lean_nat_dec_lt(v_i_1799_, v___x_1800_);
                if v___x_1801_ == 0 {
                    crate::leanh::lean_dec(v_i_1799_);
                    v___x_1802_ = crate::leanh::lean_box(0);
                    return v___x_1802_;
                } else {
                    v___x_1803_ = lean_array_fget_borrowed(v_xs_1797_, v_i_1799_);
                    v___x_1804_ = lean_name_eq(v___x_1803_, v_v_1798_);
                    if v___x_1804_ == 0 {
                        v___x_1805_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1806_ = lean_nat_add(v_i_1799_, v___x_1805_);
                        crate::leanh::lean_dec(v_i_1799_);
                        v_i_1799_ = v___x_1806_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1808_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1808_, 0, v_i_1799_);
                        return v___x_1808_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5_spec__8___boxed(
    mut v_xs_1809_: *mut crate::leanh::LeanObject,
    mut v_v_1810_: *mut crate::leanh::LeanObject,
    mut v_i_1811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1812_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5_spec__8(v_xs_1809_, v_v_1810_, v_i_1811_);
    crate::leanh::lean_dec(v_v_1810_);
    crate::leanh::lean_dec_ref(v_xs_1809_);
    return v_res_1812_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5(
    mut v_xs_1813_: *mut crate::leanh::LeanObject,
    mut v_v_1814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1815_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1816_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5_spec__8(v_xs_1813_, v_v_1814_, v___x_1815_);
    return v___x_1816_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5___boxed(
    mut v_xs_1817_: *mut crate::leanh::LeanObject,
    mut v_v_1818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1819_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5(v_xs_1817_, v_v_1818_);
    crate::leanh::lean_dec(v_v_1818_);
    crate::leanh::lean_dec_ref(v_xs_1817_);
    return v_res_1819_;
}
pub unsafe fn l_Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3(
    mut v_xs_1820_: *mut crate::leanh::LeanObject,
    mut v_v_1821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1827_: u8 = 0;
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1831_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1822_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3_spec__5(v_xs_1820_, v_v_1821_);
                if crate::leanh::lean_obj_tag(v___x_1822_) == 0 {
                    v___x_1823_ = crate::leanh::lean_box(0);
                    return v___x_1823_;
                } else {
                    v_val_1824_ = crate::leanh::lean_ctor_get(v___x_1822_, 0);
                    v_isSharedCheck_1831_ = (!crate::leanh::lean_is_exclusive(v___x_1822_)) as u8;
                    if v_isSharedCheck_1831_ == 0 {
                        v___x_1826_ = v___x_1822_;
                        v_isShared_1827_ = v_isSharedCheck_1831_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1824_);
                        crate::leanh::lean_dec(v___x_1822_);
                        v___x_1826_ = crate::leanh::lean_box(0);
                        v_isShared_1827_ = v_isSharedCheck_1831_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1827_ == 0 {
                    v___x_1829_ = v___x_1826_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1830_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_val_1824_);
                    v___x_1829_ = v_reuseFailAlloc_1830_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1829_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3___boxed(
    mut v_xs_1832_: *mut crate::leanh::LeanObject,
    mut v_v_1833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1834_ = l_Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3(v_xs_1832_, v_v_1833_);
    crate::leanh::lean_dec(v_v_1833_);
    crate::leanh::lean_dec_ref(v_xs_1832_);
    return v_res_1834_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3_spec__5(
    mut v_msgData_1835_: *mut crate::leanh::LeanObject,
    mut v___y_1836_: *mut crate::leanh::LeanObject,
    mut v___y_1837_: *mut crate::leanh::LeanObject,
    mut v___y_1838_: *mut crate::leanh::LeanObject,
    mut v___y_1839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1841_ = lean_st_ref_get(v___y_1839_);
    v_env_1842_ = crate::leanh::lean_ctor_get(v___x_1841_, 0);
    crate::leanh::lean_inc_ref(v_env_1842_);
    crate::leanh::lean_dec(v___x_1841_);
    v___x_1843_ = lean_st_ref_get(v___y_1837_);
    v_mctx_1844_ = crate::leanh::lean_ctor_get(v___x_1843_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1844_);
    crate::leanh::lean_dec(v___x_1843_);
    v_lctx_1845_ = crate::leanh::lean_ctor_get(v___y_1836_, 2);
    v_options_1846_ = crate::leanh::lean_ctor_get(v___y_1838_, 2);
    crate::leanh::lean_inc_ref(v_options_1846_);
    crate::leanh::lean_inc_ref(v_lctx_1845_);
    v___x_1847_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1847_, 0, v_env_1842_);
    crate::leanh::lean_ctor_set(v___x_1847_, 1, v_mctx_1844_);
    crate::leanh::lean_ctor_set(v___x_1847_, 2, v_lctx_1845_);
    crate::leanh::lean_ctor_set(v___x_1847_, 3, v_options_1846_);
    v___x_1848_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1848_, 0, v___x_1847_);
    crate::leanh::lean_ctor_set(v___x_1848_, 1, v_msgData_1835_);
    v___x_1849_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1849_, 0, v___x_1848_);
    return v___x_1849_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3_spec__5___boxed(
    mut v_msgData_1850_: *mut crate::leanh::LeanObject,
    mut v___y_1851_: *mut crate::leanh::LeanObject,
    mut v___y_1852_: *mut crate::leanh::LeanObject,
    mut v___y_1853_: *mut crate::leanh::LeanObject,
    mut v___y_1854_: *mut crate::leanh::LeanObject,
    mut v___y_1855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1856_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3_spec__5(v_msgData_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
    crate::leanh::lean_dec(v___y_1854_);
    crate::leanh::lean_dec_ref(v___y_1853_);
    crate::leanh::lean_dec(v___y_1852_);
    crate::leanh::lean_dec_ref(v___y_1851_);
    return v_res_1856_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___redArg(
    mut v_msg_1857_: *mut crate::leanh::LeanObject,
    mut v___y_1858_: *mut crate::leanh::LeanObject,
    mut v___y_1859_: *mut crate::leanh::LeanObject,
    mut v___y_1860_: *mut crate::leanh::LeanObject,
    mut v___y_1861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1868_: u8 = 0;
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1873_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1863_ = crate::leanh::lean_ctor_get(v___y_1860_, 5);
                v___x_1864_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3_spec__5(v_msg_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
                v_a_1865_ = crate::leanh::lean_ctor_get(v___x_1864_, 0);
                v_isSharedCheck_1873_ = (!crate::leanh::lean_is_exclusive(v___x_1864_)) as u8;
                if v_isSharedCheck_1873_ == 0 {
                    v___x_1867_ = v___x_1864_;
                    v_isShared_1868_ = v_isSharedCheck_1873_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1865_);
                    crate::leanh::lean_dec(v___x_1864_);
                    v___x_1867_ = crate::leanh::lean_box(0);
                    v_isShared_1868_ = v_isSharedCheck_1873_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1863_);
                v___x_1869_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1869_, 0, v_ref_1863_);
                crate::leanh::lean_ctor_set(v___x_1869_, 1, v_a_1865_);
                if v_isShared_1868_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1867_, 1);
                    crate::leanh::lean_ctor_set(v___x_1867_, 0, v___x_1869_);
                    v___x_1871_ = v___x_1867_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1872_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1869_);
                    v___x_1871_ = v_reuseFailAlloc_1872_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1871_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___redArg___boxed(
    mut v_msg_1874_: *mut crate::leanh::LeanObject,
    mut v___y_1875_: *mut crate::leanh::LeanObject,
    mut v___y_1876_: *mut crate::leanh::LeanObject,
    mut v___y_1877_: *mut crate::leanh::LeanObject,
    mut v___y_1878_: *mut crate::leanh::LeanObject,
    mut v___y_1879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1880_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___redArg(v_msg_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
    crate::leanh::lean_dec(v___y_1878_);
    crate::leanh::lean_dec_ref(v___y_1877_);
    crate::leanh::lean_dec(v___y_1876_);
    crate::leanh::lean_dec_ref(v___y_1875_);
    return v_res_1880_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(
    mut v_ref_1881_: *mut crate::leanh::LeanObject,
    mut v_msg_1882_: *mut crate::leanh::LeanObject,
    mut v___y_1883_: *mut crate::leanh::LeanObject,
    mut v___y_1884_: *mut crate::leanh::LeanObject,
    mut v___y_1885_: *mut crate::leanh::LeanObject,
    mut v___y_1886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1900_: u8 = 0;
    let mut v_cancelTk_x3f_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1902_: u8 = 0;
    let mut v_inheritedTraceOptions_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_1888_ = crate::leanh::lean_ctor_get(v___y_1885_, 0);
    v_fileMap_1889_ = crate::leanh::lean_ctor_get(v___y_1885_, 1);
    v_options_1890_ = crate::leanh::lean_ctor_get(v___y_1885_, 2);
    v_currRecDepth_1891_ = crate::leanh::lean_ctor_get(v___y_1885_, 3);
    v_maxRecDepth_1892_ = crate::leanh::lean_ctor_get(v___y_1885_, 4);
    v_ref_1893_ = crate::leanh::lean_ctor_get(v___y_1885_, 5);
    v_currNamespace_1894_ = crate::leanh::lean_ctor_get(v___y_1885_, 6);
    v_openDecls_1895_ = crate::leanh::lean_ctor_get(v___y_1885_, 7);
    v_initHeartbeats_1896_ = crate::leanh::lean_ctor_get(v___y_1885_, 8);
    v_maxHeartbeats_1897_ = crate::leanh::lean_ctor_get(v___y_1885_, 9);
    v_quotContext_1898_ = crate::leanh::lean_ctor_get(v___y_1885_, 10);
    v_currMacroScope_1899_ = crate::leanh::lean_ctor_get(v___y_1885_, 11);
    v_diag_1900_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1885_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1901_ = crate::leanh::lean_ctor_get(v___y_1885_, 12);
    v_suppressElabErrors_1902_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1885_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1903_ = crate::leanh::lean_ctor_get(v___y_1885_, 13);
    v_ref_1904_ = l_Lean_replaceRef(v_ref_1881_, v_ref_1893_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_1903_);
    crate::leanh::lean_inc(v_cancelTk_x3f_1901_);
    crate::leanh::lean_inc(v_currMacroScope_1899_);
    crate::leanh::lean_inc(v_quotContext_1898_);
    crate::leanh::lean_inc(v_maxHeartbeats_1897_);
    crate::leanh::lean_inc(v_initHeartbeats_1896_);
    crate::leanh::lean_inc(v_openDecls_1895_);
    crate::leanh::lean_inc(v_currNamespace_1894_);
    crate::leanh::lean_inc(v_maxRecDepth_1892_);
    crate::leanh::lean_inc(v_currRecDepth_1891_);
    crate::leanh::lean_inc_ref(v_options_1890_);
    crate::leanh::lean_inc_ref(v_fileMap_1889_);
    crate::leanh::lean_inc_ref(v_fileName_1888_);
    v___x_1905_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1905_, 0, v_fileName_1888_);
    crate::leanh::lean_ctor_set(v___x_1905_, 1, v_fileMap_1889_);
    crate::leanh::lean_ctor_set(v___x_1905_, 2, v_options_1890_);
    crate::leanh::lean_ctor_set(v___x_1905_, 3, v_currRecDepth_1891_);
    crate::leanh::lean_ctor_set(v___x_1905_, 4, v_maxRecDepth_1892_);
    crate::leanh::lean_ctor_set(v___x_1905_, 5, v_ref_1904_);
    crate::leanh::lean_ctor_set(v___x_1905_, 6, v_currNamespace_1894_);
    crate::leanh::lean_ctor_set(v___x_1905_, 7, v_openDecls_1895_);
    crate::leanh::lean_ctor_set(v___x_1905_, 8, v_initHeartbeats_1896_);
    crate::leanh::lean_ctor_set(v___x_1905_, 9, v_maxHeartbeats_1897_);
    crate::leanh::lean_ctor_set(v___x_1905_, 10, v_quotContext_1898_);
    crate::leanh::lean_ctor_set(v___x_1905_, 11, v_currMacroScope_1899_);
    crate::leanh::lean_ctor_set(v___x_1905_, 12, v_cancelTk_x3f_1901_);
    crate::leanh::lean_ctor_set(v___x_1905_, 13, v_inheritedTraceOptions_1903_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1905_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_1900_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1905_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1902_,
    );
    v___x_1906_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___redArg(v_msg_1882_, v___y_1883_, v___y_1884_, v___x_1905_, v___y_1886_);
    crate::leanh::lean_dec_ref_known(v___x_1905_, 14);
    return v___x_1906_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg___boxed(
    mut v_ref_1907_: *mut crate::leanh::LeanObject,
    mut v_msg_1908_: *mut crate::leanh::LeanObject,
    mut v___y_1909_: *mut crate::leanh::LeanObject,
    mut v___y_1910_: *mut crate::leanh::LeanObject,
    mut v___y_1911_: *mut crate::leanh::LeanObject,
    mut v___y_1912_: *mut crate::leanh::LeanObject,
    mut v___y_1913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1914_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_ref_1907_, v_msg_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
    crate::leanh::lean_dec(v___y_1912_);
    crate::leanh::lean_dec_ref(v___y_1911_);
    crate::leanh::lean_dec(v___y_1910_);
    crate::leanh::lean_dec_ref(v___y_1909_);
    crate::leanh::lean_dec(v_ref_1907_);
    return v_res_1914_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1916_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__0;
    v___x_1917_ = l_Lean_stringToMessageData(v___x_1916_);
    return v___x_1917_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__2;
    v___x_1920_ = l_Lean_stringToMessageData(v___x_1919_);
    return v___x_1920_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__4;
    v___x_1923_ = l_Lean_stringToMessageData(v___x_1922_);
    return v___x_1923_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__6;
    v___x_1926_ = l_Lean_stringToMessageData(v___x_1925_);
    return v___x_1926_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__8;
    v___x_1929_ = l_Lean_stringToMessageData(v___x_1928_);
    return v___x_1929_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1931_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__10;
    v___x_1932_ = l_Lean_stringToMessageData(v___x_1931_);
    return v___x_1932_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1934_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__12;
    v___x_1935_ = l_Lean_stringToMessageData(v___x_1934_);
    return v___x_1935_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1937_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__14;
    v___x_1938_ = l_Lean_stringToMessageData(v___x_1937_);
    return v___x_1938_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__16;
    v___x_1941_ = l_Lean_stringToMessageData(v___x_1940_);
    return v___x_1941_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__18;
    v___x_1944_ = l_Lean_stringToMessageData(v___x_1943_);
    return v___x_1944_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__20;
    v___x_1947_ = l_Lean_stringToMessageData(v___x_1946_);
    return v___x_1947_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4(
    mut v_a_1948_: *mut crate::leanh::LeanObject,
    mut v_declName_1949_: *mut crate::leanh::LeanObject,
    mut v___x_1950_: *mut crate::leanh::LeanObject,
    mut v_as_1951_: *mut crate::leanh::LeanObject,
    mut v_sz_1952_: usize,
    mut v_i_1953_: usize,
    mut v_b_1954_: *mut crate::leanh::LeanObject,
    mut v___y_1955_: *mut crate::leanh::LeanObject,
    mut v___y_1956_: *mut crate::leanh::LeanObject,
    mut v___y_1957_: *mut crate::leanh::LeanObject,
    mut v___y_1958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: usize = 0;
    let mut v___x_1963_: usize = 0;
    let mut v___y_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: u8 = 0;
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: u8 = 0;
    let mut v_a_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1977_: u8 = 0;
    let mut v___y_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: u8 = 0;
    let mut v___x_1987_: u8 = 0;
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2006_: u8 = 0;
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2010_: u8 = 0;
    let mut v_reuseFailAlloc_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2034_: u8 = 0;
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2038_: u8 = 0;
    let mut v_reuseFailAlloc_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: u8 = 0;
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2046_: u8 = 0;
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2050_: u8 = 0;
    let mut v_isSharedCheck_2051_: u8 = 0;
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: u8 = 0;
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2067_: u8 = 0;
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2071_: u8 = 0;
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2085_: u8 = 0;
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2089_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1968_ = lean_usize_dec_lt(v_i_1953_, v_sz_1952_);
                if v___x_1968_ == 0 {
                    crate::leanh::lean_dec(v_declName_1949_);
                    v___x_1969_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1969_, 0, v_b_1954_);
                    return v___x_1969_;
                } else {
                    v___x_1970_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1971_ = lean_nat_dec_eq(v___x_1950_, v___x_1970_);
                    v_a_1972_ = lean_array_uget_borrowed(v_as_1951_, v_i_1953_);
                    v___x_1973_ = l_Lean_Syntax_isNatLit_x3f(v_a_1972_);
                    if crate::leanh::lean_obj_tag(v___x_1973_) == 1 {
                        v_val_1974_ = crate::leanh::lean_ctor_get(v___x_1973_, 0);
                        v_isSharedCheck_2051_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1973_)) as u8;
                        if v_isSharedCheck_2051_ == 0 {
                            v___x_1976_ = v___x_1973_;
                            v_isShared_1977_ = v_isSharedCheck_2051_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1974_);
                            crate::leanh::lean_dec(v___x_1973_);
                            v___x_1976_ = crate::leanh::lean_box(0);
                            v_isShared_1977_ = v_isSharedCheck_2051_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1973_);
                        v___x_2052_ = l_Lean_Syntax_getId(v_a_1972_);
                        v___x_2053_ = l_Array_idxOf_x3f___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__3(v_a_1948_, v___x_2052_);
                        if crate::leanh::lean_obj_tag(v___x_2053_) == 1 {
                            v_val_2054_ = crate::leanh::lean_ctor_get(v___x_2053_, 0);
                            crate::leanh::lean_inc(v_val_2054_);
                            crate::leanh::lean_dec_ref_known(v___x_2053_, 1);
                            v___x_2057_ = l_Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1(v_b_1954_, v_val_2054_);
                            if v___x_2057_ == 0 {
                                crate::leanh::lean_dec(v___x_2052_);
                                state = 13;
                                continue;
                            } else {
                                v___x_2058_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17);
                                v___x_2059_ = l_Lean_MessageData_ofName(v___x_2052_);
                                v___x_2060_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2060_, 0, v___x_2058_);
                                crate::leanh::lean_ctor_set(v___x_2060_, 1, v___x_2059_);
                                v___x_2061_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__19), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__19_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__19);
                                v___x_2062_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2062_, 0, v___x_2060_);
                                crate::leanh::lean_ctor_set(v___x_2062_, 1, v___x_2061_);
                                v___x_2063_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_a_1972_, v___x_2062_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
                                if crate::leanh::lean_obj_tag(v___x_2063_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_2063_, 1);
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_val_2054_);
                                    crate::leanh::lean_dec_ref(v_b_1954_);
                                    crate::leanh::lean_dec(v_declName_1949_);
                                    v_a_2064_ = crate::leanh::lean_ctor_get(v___x_2063_, 0);
                                    v_isSharedCheck_2071_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2063_)) as u8;
                                    if v_isSharedCheck_2071_ == 0 {
                                        v___x_2066_ = v___x_2063_;
                                        v_isShared_2067_ = v_isSharedCheck_2071_;
                                        state = 14;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2064_);
                                        crate::leanh::lean_dec(v___x_2063_);
                                        v___x_2066_ = crate::leanh::lean_box(0);
                                        v_isShared_2067_ = v_isSharedCheck_2071_;
                                        state = 14;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_2053_);
                            v___x_2072_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__17);
                            v___x_2073_ = l_Lean_MessageData_ofName(v___x_2052_);
                            v___x_2074_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2074_, 0, v___x_2072_);
                            crate::leanh::lean_ctor_set(v___x_2074_, 1, v___x_2073_);
                            v___x_2075_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9);
                            v___x_2076_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2076_, 0, v___x_2074_);
                            crate::leanh::lean_ctor_set(v___x_2076_, 1, v___x_2075_);
                            crate::leanh::lean_inc(v_declName_1949_);
                            v___x_2077_ =
                                l_Lean_MessageData_ofConstName(v_declName_1949_, v___x_1971_);
                            v___x_2078_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2078_, 0, v___x_2076_);
                            crate::leanh::lean_ctor_set(v___x_2078_, 1, v___x_2077_);
                            v___x_2079_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__21), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__21_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__21);
                            v___x_2080_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2080_, 0, v___x_2078_);
                            crate::leanh::lean_ctor_set(v___x_2080_, 1, v___x_2079_);
                            v___x_2081_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_a_1972_, v___x_2080_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
                            if crate::leanh::lean_obj_tag(v___x_2081_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_2081_, 1);
                                v_a_1961_ = v_b_1954_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_b_1954_);
                                crate::leanh::lean_dec(v_declName_1949_);
                                v_a_2082_ = crate::leanh::lean_ctor_get(v___x_2081_, 0);
                                v_isSharedCheck_2089_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2081_)) as u8;
                                if v_isSharedCheck_2089_ == 0 {
                                    v___x_2084_ = v___x_2081_;
                                    v_isShared_2085_ = v_isSharedCheck_2089_;
                                    state = 16;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2082_);
                                    crate::leanh::lean_dec(v___x_2081_);
                                    v___x_2084_ = crate::leanh::lean_box(0);
                                    v_isShared_2085_ = v_isSharedCheck_2089_;
                                    state = 16;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1962_ = 1usize;
                v___x_1963_ = lean_usize_add(v_i_1953_, v___x_1962_);
                v_i_1953_ = v___x_1963_;
                v_b_1954_ = v_a_1961_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1967_ = lean_array_push(v_b_1954_, v___y_1966_);
                v_a_1961_ = v___x_1967_;
                state = 1;
                continue;
            }
            3 => {
                v___x_2040_ = lean_nat_dec_eq(v_val_1974_, v___x_1970_);
                if v___x_2040_ == 0 {
                    v___y_1979_ = v___y_1955_;
                    v___y_1980_ = v___y_1956_;
                    v___y_1981_ = v___y_1957_;
                    v___y_1982_ = v___y_1958_;
                    state = 4;
                    continue;
                } else {
                    v___x_2041_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__15), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__15_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__15);
                    v___x_2042_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_a_1972_, v___x_2041_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
                    if crate::leanh::lean_obj_tag(v___x_2042_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2042_, 1);
                        v___y_1979_ = v___y_1955_;
                        v___y_1980_ = v___y_1956_;
                        v___y_1981_ = v___y_1957_;
                        v___y_1982_ = v___y_1958_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_1976_);
                        crate::leanh::lean_dec(v_val_1974_);
                        crate::leanh::lean_dec_ref(v_b_1954_);
                        crate::leanh::lean_dec(v_declName_1949_);
                        v_a_2043_ = crate::leanh::lean_ctor_get(v___x_2042_, 0);
                        v_isSharedCheck_2050_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2042_)) as u8;
                        if v_isSharedCheck_2050_ == 0 {
                            v___x_2045_ = v___x_2042_;
                            v_isShared_2046_ = v_isSharedCheck_2050_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2043_);
                            crate::leanh::lean_dec(v___x_2042_);
                            v___x_2045_ = crate::leanh::lean_box(0);
                            v_isShared_2046_ = v_isSharedCheck_2050_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v___x_1983_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1984_ = lean_nat_sub(v_val_1974_, v___x_1983_);
                crate::leanh::lean_dec(v_val_1974_);
                v___x_1985_ = lean_array_get_size(v_a_1948_);
                v___x_1986_ = lean_nat_dec_le(v___x_1985_, v___x_1984_);
                if v___x_1986_ == 0 {
                    v___x_1987_ = l_Array_contains___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__1(v_b_1954_, v___x_1984_);
                    if v___x_1987_ == 0 {
                        crate::leanh::lean_del_object(v___x_1976_);
                        v___y_1966_ = v___x_1984_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1988_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__1);
                        v___x_1989_ = lean_nat_add(v___x_1984_, v___x_1983_);
                        v___x_1990_ = l_Nat_reprFast(v___x_1989_);
                        if v_isShared_1977_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_1976_, 3);
                            crate::leanh::lean_ctor_set(v___x_1976_, 0, v___x_1990_);
                            v___x_1992_ = v___x_1976_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_2011_ =
                                crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_1990_);
                            v___x_1992_ = v_reuseFailAlloc_2011_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v___x_2012_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__7);
                    v___x_2013_ = l_Nat_reprFast(v___x_1984_);
                    if v_isShared_1977_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1976_, 3);
                        crate::leanh::lean_ctor_set(v___x_1976_, 0, v___x_2013_);
                        v___x_2015_ = v___x_1976_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2039_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2013_);
                        v___x_2015_ = v_reuseFailAlloc_2039_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1993_ = l_Lean_MessageData_ofFormat(v___x_1992_);
                v___x_1994_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1994_, 0, v___x_1988_);
                crate::leanh::lean_ctor_set(v___x_1994_, 1, v___x_1993_);
                v___x_1995_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__3);
                v___x_1996_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1996_, 0, v___x_1994_);
                crate::leanh::lean_ctor_set(v___x_1996_, 1, v___x_1995_);
                v___x_1997_ = lean_array_fget_borrowed(v_a_1948_, v___x_1984_);
                crate::leanh::lean_inc(v___x_1997_);
                v___x_1998_ = l_Lean_MessageData_ofName(v___x_1997_);
                v___x_1999_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1999_, 0, v___x_1996_);
                crate::leanh::lean_ctor_set(v___x_1999_, 1, v___x_1998_);
                v___x_2000_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__5);
                v___x_2001_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2001_, 0, v___x_1999_);
                crate::leanh::lean_ctor_set(v___x_2001_, 1, v___x_2000_);
                v___x_2002_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_a_1972_, v___x_2001_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
                if crate::leanh::lean_obj_tag(v___x_2002_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2002_, 1);
                    v___y_1966_ = v___x_1984_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_1984_);
                    crate::leanh::lean_dec_ref(v_b_1954_);
                    crate::leanh::lean_dec(v_declName_1949_);
                    v_a_2003_ = crate::leanh::lean_ctor_get(v___x_2002_, 0);
                    v_isSharedCheck_2010_ = (!crate::leanh::lean_is_exclusive(v___x_2002_)) as u8;
                    if v_isSharedCheck_2010_ == 0 {
                        v___x_2005_ = v___x_2002_;
                        v_isShared_2006_ = v_isSharedCheck_2010_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2003_);
                        crate::leanh::lean_dec(v___x_2002_);
                        v___x_2005_ = crate::leanh::lean_box(0);
                        v_isShared_2006_ = v_isSharedCheck_2010_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_2006_ == 0 {
                    v___x_2008_ = v___x_2005_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2009_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_2003_);
                    v___x_2008_ = v_reuseFailAlloc_2009_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2008_;
            }
            8 => {
                v___x_2016_ = l_Lean_MessageData_ofFormat(v___x_2015_);
                v___x_2017_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2017_, 0, v___x_2012_);
                crate::leanh::lean_ctor_set(v___x_2017_, 1, v___x_2016_);
                v___x_2018_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__9);
                v___x_2019_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2019_, 0, v___x_2017_);
                crate::leanh::lean_ctor_set(v___x_2019_, 1, v___x_2018_);
                crate::leanh::lean_inc(v_declName_1949_);
                v___x_2020_ = l_Lean_MessageData_ofConstName(v_declName_1949_, v___x_1971_);
                v___x_2021_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2021_, 0, v___x_2019_);
                crate::leanh::lean_ctor_set(v___x_2021_, 1, v___x_2020_);
                v___x_2022_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__11), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__11_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__11);
                v___x_2023_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2023_, 0, v___x_2021_);
                crate::leanh::lean_ctor_set(v___x_2023_, 1, v___x_2022_);
                v___x_2024_ = l_Nat_reprFast(v___x_1985_);
                v___x_2025_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2025_, 0, v___x_2024_);
                v___x_2026_ = l_Lean_MessageData_ofFormat(v___x_2025_);
                v___x_2027_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2027_, 0, v___x_2023_);
                crate::leanh::lean_ctor_set(v___x_2027_, 1, v___x_2026_);
                v___x_2028_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__13), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__13_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___closed__13);
                v___x_2029_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2029_, 0, v___x_2027_);
                crate::leanh::lean_ctor_set(v___x_2029_, 1, v___x_2028_);
                v___x_2030_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_a_1972_, v___x_2029_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
                if crate::leanh::lean_obj_tag(v___x_2030_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2030_, 1);
                    v_a_1961_ = v_b_1954_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_b_1954_);
                    crate::leanh::lean_dec(v_declName_1949_);
                    v_a_2031_ = crate::leanh::lean_ctor_get(v___x_2030_, 0);
                    v_isSharedCheck_2038_ = (!crate::leanh::lean_is_exclusive(v___x_2030_)) as u8;
                    if v_isSharedCheck_2038_ == 0 {
                        v___x_2033_ = v___x_2030_;
                        v_isShared_2034_ = v_isSharedCheck_2038_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2031_);
                        crate::leanh::lean_dec(v___x_2030_);
                        v___x_2033_ = crate::leanh::lean_box(0);
                        v_isShared_2034_ = v_isSharedCheck_2038_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_2034_ == 0 {
                    v___x_2036_ = v___x_2033_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2037_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
                    v___x_2036_ = v_reuseFailAlloc_2037_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2036_;
            }
            11 => {
                if v_isShared_2046_ == 0 {
                    v___x_2048_ = v___x_2045_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2049_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
                    v___x_2048_ = v_reuseFailAlloc_2049_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2048_;
            }
            13 => {
                v___x_2056_ = lean_array_push(v_b_1954_, v_val_2054_);
                v_a_1961_ = v___x_2056_;
                state = 1;
                continue;
            }
            14 => {
                if v_isShared_2067_ == 0 {
                    v___x_2069_ = v___x_2066_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2070_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
                    v___x_2069_ = v_reuseFailAlloc_2070_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2069_;
            }
            16 => {
                if v_isShared_2085_ == 0 {
                    v___x_2087_ = v___x_2084_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2088_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
                    v___x_2087_ = v_reuseFailAlloc_2088_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2087_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4___boxed(
    mut v_a_2090_: *mut crate::leanh::LeanObject,
    mut v_declName_2091_: *mut crate::leanh::LeanObject,
    mut v___x_2092_: *mut crate::leanh::LeanObject,
    mut v_as_2093_: *mut crate::leanh::LeanObject,
    mut v_sz_2094_: *mut crate::leanh::LeanObject,
    mut v_i_2095_: *mut crate::leanh::LeanObject,
    mut v_b_2096_: *mut crate::leanh::LeanObject,
    mut v___y_2097_: *mut crate::leanh::LeanObject,
    mut v___y_2098_: *mut crate::leanh::LeanObject,
    mut v___y_2099_: *mut crate::leanh::LeanObject,
    mut v___y_2100_: *mut crate::leanh::LeanObject,
    mut v___y_2101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2102_: usize = 0;
    let mut v_i_boxed_2103_: usize = 0;
    let mut v_res_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2102_ = crate::leanh::lean_unbox_usize(v_sz_2094_);
    crate::leanh::lean_dec(v_sz_2094_);
    v_i_boxed_2103_ = crate::leanh::lean_unbox_usize(v_i_2095_);
    crate::leanh::lean_dec(v_i_2095_);
    v_res_2104_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4(v_a_2090_, v_declName_2091_, v___x_2092_, v_as_2093_, v_sz_boxed_2102_, v_i_boxed_2103_, v_b_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
    crate::leanh::lean_dec(v___y_2100_);
    crate::leanh::lean_dec_ref(v___y_2099_);
    crate::leanh::lean_dec(v___y_2098_);
    crate::leanh::lean_dec_ref(v___y_2097_);
    crate::leanh::lean_dec_ref(v_as_2093_);
    crate::leanh::lean_dec(v___x_2092_);
    crate::leanh::lean_dec_ref(v_a_2090_);
    return v_res_2104_;
}
pub unsafe fn l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___lam__0(
    mut v___x_2105_: *mut crate::leanh::LeanObject,
    mut v_args_2106_: *mut crate::leanh::LeanObject,
    mut v_declName_2107_: *mut crate::leanh::LeanObject,
    mut v___x_2108_: *mut crate::leanh::LeanObject,
    mut v_xs_2109_: *mut crate::leanh::LeanObject,
    mut v_x_2110_: *mut crate::leanh::LeanObject,
    mut v___y_2111_: *mut crate::leanh::LeanObject,
    mut v___y_2112_: *mut crate::leanh::LeanObject,
    mut v___y_2113_: *mut crate::leanh::LeanObject,
    mut v___y_2114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_2116_: usize = 0;
    let mut v___x_2117_: usize = 0;
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2122_: u8 = 0;
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2124_: usize = 0;
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: u8 = 0;
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: u8 = 0;
    let mut v___x_2141_: u8 = 0;
    let mut v_isSharedCheck_2142_: u8 = 0;
    let mut v_a_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2146_: u8 = 0;
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2150_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_2116_ = lean_array_size(v_xs_2109_);
                v___x_2117_ = 0usize;
                v___x_2118_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___redArg(v_sz_2116_, v___x_2117_, v_xs_2109_, v___y_2111_, v___y_2113_, v___y_2114_);
                if crate::leanh::lean_obj_tag(v___x_2118_) == 0 {
                    v_a_2119_ = crate::leanh::lean_ctor_get(v___x_2118_, 0);
                    v_isSharedCheck_2142_ = (!crate::leanh::lean_is_exclusive(v___x_2118_)) as u8;
                    if v_isSharedCheck_2142_ == 0 {
                        v___x_2121_ = v___x_2118_;
                        v_isShared_2122_ = v_isSharedCheck_2142_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2119_);
                        crate::leanh::lean_dec(v___x_2118_);
                        v___x_2121_ = crate::leanh::lean_box(0);
                        v_isShared_2122_ = v_isSharedCheck_2142_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_2107_);
                    crate::leanh::lean_dec(v___x_2105_);
                    v_a_2143_ = crate::leanh::lean_ctor_get(v___x_2118_, 0);
                    v_isSharedCheck_2150_ = (!crate::leanh::lean_is_exclusive(v___x_2118_)) as u8;
                    if v_isSharedCheck_2150_ == 0 {
                        v___x_2145_ = v___x_2118_;
                        v_isShared_2146_ = v_isSharedCheck_2150_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2143_);
                        crate::leanh::lean_dec(v___x_2118_);
                        v___x_2145_ = crate::leanh::lean_box(0);
                        v_isShared_2146_ = v_isSharedCheck_2150_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2123_ = lean_mk_empty_array_with_capacity(v___x_2105_);
                v_sz_2124_ = lean_array_size(v_args_2106_);
                v___x_2125_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__4(v_a_2119_, v_declName_2107_, v___x_2108_, v_args_2106_, v_sz_2124_, v___x_2117_, v___x_2123_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
                crate::leanh::lean_dec(v_a_2119_);
                if crate::leanh::lean_obj_tag(v___x_2125_) == 0 {
                    v_a_2126_ = crate::leanh::lean_ctor_get(v___x_2125_, 0);
                    crate::leanh::lean_inc(v_a_2126_);
                    v___x_2127_ = lean_array_get_size(v_a_2126_);
                    v___x_2135_ = lean_nat_dec_eq(v___x_2127_, v___x_2105_);
                    if v___x_2135_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2125_, 1);
                        v___x_2136_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2137_ = lean_nat_sub(v___x_2127_, v___x_2136_);
                        v___x_2141_ = lean_nat_dec_le(v___x_2105_, v___x_2137_);
                        if v___x_2141_ == 0 {
                            crate::leanh::lean_dec(v___x_2105_);
                            crate::leanh::lean_inc(v___x_2137_);
                            v___y_2139_ = v___x_2137_;
                            state = 4;
                            continue;
                        } else {
                            v___y_2139_ = v___x_2105_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2126_);
                        crate::leanh::lean_del_object(v___x_2121_);
                        crate::leanh::lean_dec(v___x_2105_);
                        return v___x_2125_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2121_);
                    crate::leanh::lean_dec(v___x_2105_);
                    return v___x_2125_;
                }
            }
            2 => {
                v___x_2131_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg(v___x_2127_, v_a_2126_, v___y_2129_, v___y_2130_);
                crate::leanh::lean_dec(v___y_2130_);
                if v_isShared_2122_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2121_, 0, v___x_2131_);
                    v___x_2133_ = v___x_2121_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2134_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2131_);
                    v___x_2133_ = v_reuseFailAlloc_2134_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2133_;
            }
            4 => {
                v___x_2140_ = lean_nat_dec_le(v___y_2139_, v___x_2137_);
                if v___x_2140_ == 0 {
                    crate::leanh::lean_dec(v___x_2137_);
                    crate::leanh::lean_inc(v___y_2139_);
                    v___y_2129_ = v___y_2139_;
                    v___y_2130_ = v___y_2139_;
                    state = 2;
                    continue;
                } else {
                    v___y_2129_ = v___y_2139_;
                    v___y_2130_ = v___x_2137_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                if v_isShared_2146_ == 0 {
                    v___x_2148_ = v___x_2145_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2149_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2143_);
                    v___x_2148_ = v_reuseFailAlloc_2149_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2148_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___lam__0___boxed(
    mut v___x_2151_: *mut crate::leanh::LeanObject,
    mut v_args_2152_: *mut crate::leanh::LeanObject,
    mut v_declName_2153_: *mut crate::leanh::LeanObject,
    mut v___x_2154_: *mut crate::leanh::LeanObject,
    mut v_xs_2155_: *mut crate::leanh::LeanObject,
    mut v_x_2156_: *mut crate::leanh::LeanObject,
    mut v___y_2157_: *mut crate::leanh::LeanObject,
    mut v___y_2158_: *mut crate::leanh::LeanObject,
    mut v___y_2159_: *mut crate::leanh::LeanObject,
    mut v___y_2160_: *mut crate::leanh::LeanObject,
    mut v___y_2161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2162_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___lam__0(
        v___x_2151_,
        v_args_2152_,
        v_declName_2153_,
        v___x_2154_,
        v_xs_2155_,
        v_x_2156_,
        v___y_2157_,
        v___y_2158_,
        v___y_2159_,
        v___y_2160_,
    );
    crate::leanh::lean_dec(v___y_2160_);
    crate::leanh::lean_dec_ref(v___y_2159_);
    crate::leanh::lean_dec(v___y_2158_);
    crate::leanh::lean_dec_ref(v___y_2157_);
    crate::leanh::lean_dec_ref(v_x_2156_);
    crate::leanh::lean_dec(v___x_2154_);
    crate::leanh::lean_dec_ref(v_args_2152_);
    return v_res_2162_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2163_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2163_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2164_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__0);
    v___x_2165_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2165_, 0, v___x_2164_);
    return v___x_2165_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2166_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1);
    v___x_2167_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2168_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2168_, 0, v___x_2167_);
    crate::leanh::lean_ctor_set(v___x_2168_, 1, v___x_2167_);
    crate::leanh::lean_ctor_set(v___x_2168_, 2, v___x_2167_);
    crate::leanh::lean_ctor_set(v___x_2168_, 3, v___x_2167_);
    crate::leanh::lean_ctor_set(v___x_2168_, 4, v___x_2166_);
    crate::leanh::lean_ctor_set(v___x_2168_, 5, v___x_2166_);
    crate::leanh::lean_ctor_set(v___x_2168_, 6, v___x_2166_);
    crate::leanh::lean_ctor_set(v___x_2168_, 7, v___x_2166_);
    crate::leanh::lean_ctor_set(v___x_2168_, 8, v___x_2166_);
    crate::leanh::lean_ctor_set(v___x_2168_, 9, v___x_2166_);
    return v___x_2168_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2169_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2170_ = lean_mk_empty_array_with_capacity(v___x_2169_);
    v___x_2171_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2171_, 0, v___x_2170_);
    return v___x_2171_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2172_: usize = 0;
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2172_ = 5usize;
    v___x_2173_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2174_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2175_ = lean_mk_empty_array_with_capacity(v___x_2174_);
    v___x_2176_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__3);
    v___x_2177_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_2177_, 0, v___x_2176_);
    crate::leanh::lean_ctor_set(v___x_2177_, 1, v___x_2175_);
    crate::leanh::lean_ctor_set(v___x_2177_, 2, v___x_2173_);
    crate::leanh::lean_ctor_set(v___x_2177_, 3, v___x_2173_);
    crate::leanh::lean_ctor_set_usize(v___x_2177_, 4, v___x_2172_);
    return v___x_2177_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2178_ = crate::leanh::lean_box(1);
    v___x_2179_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4);
    v___x_2180_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__1);
    v___x_2181_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2181_, 0, v___x_2180_);
    crate::leanh::lean_ctor_set(v___x_2181_, 1, v___x_2179_);
    crate::leanh::lean_ctor_set(v___x_2181_, 2, v___x_2178_);
    return v___x_2181_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2183_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__6;
    v___x_2184_ = l_Lean_stringToMessageData(v___x_2183_);
    return v___x_2184_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2186_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__8;
    v___x_2187_ = l_Lean_stringToMessageData(v___x_2186_);
    return v___x_2187_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2189_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__10;
    v___x_2190_ = l_Lean_stringToMessageData(v___x_2189_);
    return v___x_2190_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2192_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__12;
    v___x_2193_ = l_Lean_stringToMessageData(v___x_2192_);
    return v___x_2193_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2195_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__14;
    v___x_2196_ = l_Lean_stringToMessageData(v___x_2195_);
    return v___x_2196_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2198_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__16;
    v___x_2199_ = l_Lean_stringToMessageData(v___x_2198_);
    return v___x_2199_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2201_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__18;
    v___x_2202_ = l_Lean_stringToMessageData(v___x_2201_);
    return v___x_2202_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg(
    mut v_msg_2203_: *mut crate::leanh::LeanObject,
    mut v_declHint_2204_: *mut crate::leanh::LeanObject,
    mut v___y_2205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: u8 = 0;
    let mut v_isExporting_2210_: u8 = 0;
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: u8 = 0;
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2232_: u8 = 0;
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: u8 = 0;
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2264_: u8 = 0;
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2207_ = lean_st_ref_get(v___y_2205_);
                v_env_2208_ = crate::leanh::lean_ctor_get(v___x_2207_, 0);
                crate::leanh::lean_inc_ref(v_env_2208_);
                crate::leanh::lean_dec(v___x_2207_);
                v___x_2209_ = l_Lean_Name_isAnonymous(v_declHint_2204_);
                if v___x_2209_ == 0 {
                    v_isExporting_2210_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_2208_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_2210_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_2208_);
                        crate::leanh::lean_dec(v_declHint_2204_);
                        v___x_2211_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2211_, 0, v_msg_2203_);
                        return v___x_2211_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_2208_);
                        v___x_2212_ = l_Lean_Environment_setExporting(v_env_2208_, v___x_2209_);
                        crate::leanh::lean_inc(v_declHint_2204_);
                        crate::leanh::lean_inc_ref(v___x_2212_);
                        v___x_2213_ = l_Lean_Environment_contains(
                            v___x_2212_,
                            v_declHint_2204_,
                            v_isExporting_2210_,
                        );
                        if v___x_2213_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2212_);
                            crate::leanh::lean_dec_ref(v_env_2208_);
                            crate::leanh::lean_dec(v_declHint_2204_);
                            v___x_2214_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2214_, 0, v_msg_2203_);
                            return v___x_2214_;
                        } else {
                            v___x_2215_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__2);
                            v___x_2216_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__5);
                            v___x_2217_ = l_Lean_Options_empty;
                            v___x_2218_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2218_, 0, v___x_2212_);
                            crate::leanh::lean_ctor_set(v___x_2218_, 1, v___x_2215_);
                            crate::leanh::lean_ctor_set(v___x_2218_, 2, v___x_2216_);
                            crate::leanh::lean_ctor_set(v___x_2218_, 3, v___x_2217_);
                            crate::leanh::lean_inc(v_declHint_2204_);
                            v___x_2219_ =
                                l_Lean_MessageData_ofConstName(v_declHint_2204_, v___x_2209_);
                            v_c_2220_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_2220_, 0, v___x_2218_);
                            crate::leanh::lean_ctor_set(v_c_2220_, 1, v___x_2219_);
                            v___x_2221_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_2208_,
                                v_declHint_2204_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2221_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_2208_);
                                crate::leanh::lean_dec(v_declHint_2204_);
                                v___x_2222_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7);
                                v___x_2223_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2223_, 0, v___x_2222_);
                                crate::leanh::lean_ctor_set(v___x_2223_, 1, v_c_2220_);
                                v___x_2224_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__9);
                                v___x_2225_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2225_, 0, v___x_2223_);
                                crate::leanh::lean_ctor_set(v___x_2225_, 1, v___x_2224_);
                                v___x_2226_ = l_Lean_MessageData_note(v___x_2225_);
                                v___x_2227_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2227_, 0, v_msg_2203_);
                                crate::leanh::lean_ctor_set(v___x_2227_, 1, v___x_2226_);
                                v___x_2228_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2228_, 0, v___x_2227_);
                                return v___x_2228_;
                            } else {
                                v_val_2229_ = crate::leanh::lean_ctor_get(v___x_2221_, 0);
                                v_isSharedCheck_2264_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2221_)) as u8;
                                if v_isSharedCheck_2264_ == 0 {
                                    v___x_2231_ = v___x_2221_;
                                    v_isShared_2232_ = v_isSharedCheck_2264_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_2229_);
                                    crate::leanh::lean_dec(v___x_2221_);
                                    v___x_2231_ = crate::leanh::lean_box(0);
                                    v_isShared_2232_ = v_isSharedCheck_2264_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_2208_);
                    crate::leanh::lean_dec(v_declHint_2204_);
                    v___x_2265_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2265_, 0, v_msg_2203_);
                    return v___x_2265_;
                }
            }
            1 => {
                v___x_2233_ = crate::leanh::lean_box(0);
                v___x_2234_ = l_Lean_Environment_header(v_env_2208_);
                crate::leanh::lean_dec_ref(v_env_2208_);
                v___x_2235_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2234_);
                v_mod_2236_ = lean_array_get(v___x_2233_, v___x_2235_, v_val_2229_);
                crate::leanh::lean_dec(v_val_2229_);
                crate::leanh::lean_dec_ref(v___x_2235_);
                v___x_2237_ = l_Lean_isPrivateName(v_declHint_2204_);
                crate::leanh::lean_dec(v_declHint_2204_);
                if v___x_2237_ == 0 {
                    v___x_2238_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__11);
                    v___x_2239_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2239_, 0, v___x_2238_);
                    crate::leanh::lean_ctor_set(v___x_2239_, 1, v_c_2220_);
                    v___x_2240_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__13);
                    v___x_2241_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2241_, 0, v___x_2239_);
                    crate::leanh::lean_ctor_set(v___x_2241_, 1, v___x_2240_);
                    v___x_2242_ = l_Lean_MessageData_ofName(v_mod_2236_);
                    v___x_2243_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2243_, 0, v___x_2241_);
                    crate::leanh::lean_ctor_set(v___x_2243_, 1, v___x_2242_);
                    v___x_2244_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__15);
                    v___x_2245_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2245_, 0, v___x_2243_);
                    crate::leanh::lean_ctor_set(v___x_2245_, 1, v___x_2244_);
                    v___x_2246_ = l_Lean_MessageData_note(v___x_2245_);
                    v___x_2247_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2247_, 0, v_msg_2203_);
                    crate::leanh::lean_ctor_set(v___x_2247_, 1, v___x_2246_);
                    if v_isShared_2232_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2231_, 0);
                        crate::leanh::lean_ctor_set(v___x_2231_, 0, v___x_2247_);
                        v___x_2249_ = v___x_2231_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2250_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2250_, 0, v___x_2247_);
                        v___x_2249_ = v_reuseFailAlloc_2250_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2251_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__7);
                    v___x_2252_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2252_, 0, v___x_2251_);
                    crate::leanh::lean_ctor_set(v___x_2252_, 1, v_c_2220_);
                    v___x_2253_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__17);
                    v___x_2254_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2254_, 0, v___x_2252_);
                    crate::leanh::lean_ctor_set(v___x_2254_, 1, v___x_2253_);
                    v___x_2255_ = l_Lean_MessageData_ofName(v_mod_2236_);
                    v___x_2256_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2256_, 0, v___x_2254_);
                    crate::leanh::lean_ctor_set(v___x_2256_, 1, v___x_2255_);
                    v___x_2257_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__19);
                    v___x_2258_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2258_, 0, v___x_2256_);
                    crate::leanh::lean_ctor_set(v___x_2258_, 1, v___x_2257_);
                    v___x_2259_ = l_Lean_MessageData_note(v___x_2258_);
                    v___x_2260_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2260_, 0, v_msg_2203_);
                    crate::leanh::lean_ctor_set(v___x_2260_, 1, v___x_2259_);
                    if v_isShared_2232_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2231_, 0);
                        crate::leanh::lean_ctor_set(v___x_2231_, 0, v___x_2260_);
                        v___x_2262_ = v___x_2231_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2263_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2263_, 0, v___x_2260_);
                        v___x_2262_ = v_reuseFailAlloc_2263_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2249_;
            }
            3 => {
                return v___x_2262_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___boxed(
    mut v_msg_2266_: *mut crate::leanh::LeanObject,
    mut v_declHint_2267_: *mut crate::leanh::LeanObject,
    mut v___y_2268_: *mut crate::leanh::LeanObject,
    mut v___y_2269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2270_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg(v_msg_2266_, v_declHint_2267_, v___y_2268_);
    crate::leanh::lean_dec(v___y_2268_);
    return v_res_2270_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16(
    mut v_msg_2271_: *mut crate::leanh::LeanObject,
    mut v_declHint_2272_: *mut crate::leanh::LeanObject,
    mut v___y_2273_: *mut crate::leanh::LeanObject,
    mut v___y_2274_: *mut crate::leanh::LeanObject,
    mut v___y_2275_: *mut crate::leanh::LeanObject,
    mut v___y_2276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2282_: u8 = 0;
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2288_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2278_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg(v_msg_2271_, v_declHint_2272_, v___y_2276_);
                v_a_2279_ = crate::leanh::lean_ctor_get(v___x_2278_, 0);
                v_isSharedCheck_2288_ = (!crate::leanh::lean_is_exclusive(v___x_2278_)) as u8;
                if v_isSharedCheck_2288_ == 0 {
                    v___x_2281_ = v___x_2278_;
                    v_isShared_2282_ = v_isSharedCheck_2288_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2279_);
                    crate::leanh::lean_dec(v___x_2278_);
                    v___x_2281_ = crate::leanh::lean_box(0);
                    v_isShared_2282_ = v_isSharedCheck_2288_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2283_ = l_Lean_unknownIdentifierMessageTag;
                v___x_2284_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2284_, 0, v___x_2283_);
                crate::leanh::lean_ctor_set(v___x_2284_, 1, v_a_2279_);
                if v_isShared_2282_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2281_, 0, v___x_2284_);
                    v___x_2286_ = v___x_2281_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2287_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2287_, 0, v___x_2284_);
                    v___x_2286_ = v_reuseFailAlloc_2287_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2286_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16___boxed(
    mut v_msg_2289_: *mut crate::leanh::LeanObject,
    mut v_declHint_2290_: *mut crate::leanh::LeanObject,
    mut v___y_2291_: *mut crate::leanh::LeanObject,
    mut v___y_2292_: *mut crate::leanh::LeanObject,
    mut v___y_2293_: *mut crate::leanh::LeanObject,
    mut v___y_2294_: *mut crate::leanh::LeanObject,
    mut v___y_2295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2296_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16(v_msg_2289_, v_declHint_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
    crate::leanh::lean_dec(v___y_2294_);
    crate::leanh::lean_dec_ref(v___y_2293_);
    crate::leanh::lean_dec(v___y_2292_);
    crate::leanh::lean_dec_ref(v___y_2291_);
    return v_res_2296_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15___redArg(
    mut v_ref_2297_: *mut crate::leanh::LeanObject,
    mut v_msg_2298_: *mut crate::leanh::LeanObject,
    mut v_declHint_2299_: *mut crate::leanh::LeanObject,
    mut v___y_2300_: *mut crate::leanh::LeanObject,
    mut v___y_2301_: *mut crate::leanh::LeanObject,
    mut v___y_2302_: *mut crate::leanh::LeanObject,
    mut v___y_2303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2305_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16(v_msg_2298_, v_declHint_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
    v_a_2306_ = crate::leanh::lean_ctor_get(v___x_2305_, 0);
    crate::leanh::lean_inc(v_a_2306_);
    crate::leanh::lean_dec_ref(v___x_2305_);
    v___x_2307_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_ref_2297_, v_a_2306_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
    return v___x_2307_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15___redArg___boxed(
    mut v_ref_2308_: *mut crate::leanh::LeanObject,
    mut v_msg_2309_: *mut crate::leanh::LeanObject,
    mut v_declHint_2310_: *mut crate::leanh::LeanObject,
    mut v___y_2311_: *mut crate::leanh::LeanObject,
    mut v___y_2312_: *mut crate::leanh::LeanObject,
    mut v___y_2313_: *mut crate::leanh::LeanObject,
    mut v___y_2314_: *mut crate::leanh::LeanObject,
    mut v___y_2315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2316_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15___redArg(v_ref_2308_, v_msg_2309_, v_declHint_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
    crate::leanh::lean_dec(v___y_2314_);
    crate::leanh::lean_dec_ref(v___y_2313_);
    crate::leanh::lean_dec(v___y_2312_);
    crate::leanh::lean_dec_ref(v___y_2311_);
    crate::leanh::lean_dec(v_ref_2308_);
    return v_res_2316_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2318_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__0;
    v___x_2319_ = l_Lean_stringToMessageData(v___x_2318_);
    return v___x_2319_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2321_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__2;
    v___x_2322_ = l_Lean_stringToMessageData(v___x_2321_);
    return v___x_2322_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg(
    mut v_ref_2323_: *mut crate::leanh::LeanObject,
    mut v_constName_2324_: *mut crate::leanh::LeanObject,
    mut v___y_2325_: *mut crate::leanh::LeanObject,
    mut v___y_2326_: *mut crate::leanh::LeanObject,
    mut v___y_2327_: *mut crate::leanh::LeanObject,
    mut v___y_2328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: u8 = 0;
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2330_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__1);
    v___x_2331_ = 0;
    crate::leanh::lean_inc(v_constName_2324_);
    v___x_2332_ = l_Lean_MessageData_ofConstName(v_constName_2324_, v___x_2331_);
    v___x_2333_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2333_, 0, v___x_2330_);
    crate::leanh::lean_ctor_set(v___x_2333_, 1, v___x_2332_);
    v___x_2334_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___closed__3);
    v___x_2335_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2335_, 0, v___x_2333_);
    crate::leanh::lean_ctor_set(v___x_2335_, 1, v___x_2334_);
    v___x_2336_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15___redArg(v_ref_2323_, v___x_2335_, v_constName_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
    return v___x_2336_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg___boxed(
    mut v_ref_2337_: *mut crate::leanh::LeanObject,
    mut v_constName_2338_: *mut crate::leanh::LeanObject,
    mut v___y_2339_: *mut crate::leanh::LeanObject,
    mut v___y_2340_: *mut crate::leanh::LeanObject,
    mut v___y_2341_: *mut crate::leanh::LeanObject,
    mut v___y_2342_: *mut crate::leanh::LeanObject,
    mut v___y_2343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2344_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg(v_ref_2337_, v_constName_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
    crate::leanh::lean_dec(v___y_2342_);
    crate::leanh::lean_dec_ref(v___y_2341_);
    crate::leanh::lean_dec(v___y_2340_);
    crate::leanh::lean_dec_ref(v___y_2339_);
    crate::leanh::lean_dec(v_ref_2337_);
    return v_res_2344_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10___redArg(
    mut v_constName_2345_: *mut crate::leanh::LeanObject,
    mut v___y_2346_: *mut crate::leanh::LeanObject,
    mut v___y_2347_: *mut crate::leanh::LeanObject,
    mut v___y_2348_: *mut crate::leanh::LeanObject,
    mut v___y_2349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_2351_ = crate::leanh::lean_ctor_get(v___y_2348_, 5);
    v___x_2352_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg(v_ref_2351_, v_constName_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
    return v___x_2352_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10___redArg___boxed(
    mut v_constName_2353_: *mut crate::leanh::LeanObject,
    mut v___y_2354_: *mut crate::leanh::LeanObject,
    mut v___y_2355_: *mut crate::leanh::LeanObject,
    mut v___y_2356_: *mut crate::leanh::LeanObject,
    mut v___y_2357_: *mut crate::leanh::LeanObject,
    mut v___y_2358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2359_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10___redArg(v_constName_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
    crate::leanh::lean_dec(v___y_2357_);
    crate::leanh::lean_dec_ref(v___y_2356_);
    crate::leanh::lean_dec(v___y_2355_);
    crate::leanh::lean_dec_ref(v___y_2354_);
    return v_res_2359_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6(
    mut v_constName_2360_: *mut crate::leanh::LeanObject,
    mut v___y_2361_: *mut crate::leanh::LeanObject,
    mut v___y_2362_: *mut crate::leanh::LeanObject,
    mut v___y_2363_: *mut crate::leanh::LeanObject,
    mut v___y_2364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: u8 = 0;
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2374_: u8 = 0;
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2378_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2366_ = lean_st_ref_get(v___y_2364_);
                v_env_2367_ = crate::leanh::lean_ctor_get(v___x_2366_, 0);
                crate::leanh::lean_inc_ref(v_env_2367_);
                crate::leanh::lean_dec(v___x_2366_);
                v___x_2368_ = 0;
                crate::leanh::lean_inc(v_constName_2360_);
                v___x_2369_ =
                    l_Lean_Environment_find_x3f(v_env_2367_, v_constName_2360_, v___x_2368_);
                if crate::leanh::lean_obj_tag(v___x_2369_) == 0 {
                    v___x_2370_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10___redArg(v_constName_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
                    return v___x_2370_;
                } else {
                    crate::leanh::lean_dec(v_constName_2360_);
                    v_val_2371_ = crate::leanh::lean_ctor_get(v___x_2369_, 0);
                    v_isSharedCheck_2378_ = (!crate::leanh::lean_is_exclusive(v___x_2369_)) as u8;
                    if v_isSharedCheck_2378_ == 0 {
                        v___x_2373_ = v___x_2369_;
                        v_isShared_2374_ = v_isSharedCheck_2378_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2371_);
                        crate::leanh::lean_dec(v___x_2369_);
                        v___x_2373_ = crate::leanh::lean_box(0);
                        v_isShared_2374_ = v_isSharedCheck_2378_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2374_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2373_, 0);
                    v___x_2376_ = v___x_2373_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2377_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_val_2371_);
                    v___x_2376_ = v_reuseFailAlloc_2377_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2376_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6___boxed(
    mut v_constName_2379_: *mut crate::leanh::LeanObject,
    mut v___y_2380_: *mut crate::leanh::LeanObject,
    mut v___y_2381_: *mut crate::leanh::LeanObject,
    mut v___y_2382_: *mut crate::leanh::LeanObject,
    mut v___y_2383_: *mut crate::leanh::LeanObject,
    mut v___y_2384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2385_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6(v_constName_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
    crate::leanh::lean_dec(v___y_2383_);
    crate::leanh::lean_dec_ref(v___y_2382_);
    crate::leanh::lean_dec(v___y_2381_);
    crate::leanh::lean_dec_ref(v___y_2380_);
    return v_res_2385_;
}
pub unsafe fn l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs(
    mut v_declName_2388_: *mut crate::leanh::LeanObject,
    mut v_args_2389_: *mut crate::leanh::LeanObject,
    mut v_a_2390_: *mut crate::leanh::LeanObject,
    mut v_a_2391_: *mut crate::leanh::LeanObject,
    mut v_a_2392_: *mut crate::leanh::LeanObject,
    mut v_a_2393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: u8 = 0;
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2406_: u8 = 0;
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2410_: u8 = 0;
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2395_ = lean_array_get_size(v_args_2389_);
                v___x_2396_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2397_ = lean_nat_dec_eq(v___x_2395_, v___x_2396_);
                if v___x_2397_ == 0 {
                    crate::leanh::lean_inc(v_declName_2388_);
                    v___x_2398_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6(v_declName_2388_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
                    if crate::leanh::lean_obj_tag(v___x_2398_) == 0 {
                        v_a_2399_ = crate::leanh::lean_ctor_get(v___x_2398_, 0);
                        crate::leanh::lean_inc(v_a_2399_);
                        crate::leanh::lean_dec_ref_known(v___x_2398_, 1);
                        v___f_2400_ = crate::leanh::lean_alloc_closure(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___lam__0___boxed as *mut core::ffi::c_void, 11, 4);
                        crate::leanh::lean_closure_set(v___f_2400_, 0, v___x_2396_);
                        crate::leanh::lean_closure_set(v___f_2400_, 1, v_args_2389_);
                        crate::leanh::lean_closure_set(v___f_2400_, 2, v_declName_2388_);
                        crate::leanh::lean_closure_set(v___f_2400_, 3, v___x_2395_);
                        v___x_2401_ = l_Lean_ConstantInfo_type(v_a_2399_);
                        crate::leanh::lean_dec(v_a_2399_);
                        v___x_2402_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__7___redArg(v___x_2401_, v___f_2400_, v___x_2397_, v___x_2397_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
                        return v___x_2402_;
                    } else {
                        crate::leanh::lean_dec_ref(v_args_2389_);
                        crate::leanh::lean_dec(v_declName_2388_);
                        v_a_2403_ = crate::leanh::lean_ctor_get(v___x_2398_, 0);
                        v_isSharedCheck_2410_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2398_)) as u8;
                        if v_isSharedCheck_2410_ == 0 {
                            v___x_2405_ = v___x_2398_;
                            v_isShared_2406_ = v_isSharedCheck_2410_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2403_);
                            crate::leanh::lean_dec(v___x_2398_);
                            v___x_2405_ = crate::leanh::lean_box(0);
                            v_isShared_2406_ = v_isSharedCheck_2410_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_args_2389_);
                    crate::leanh::lean_dec(v_declName_2388_);
                    v___x_2411_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___closed__0;
                    v___x_2412_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2412_, 0, v___x_2411_);
                    return v___x_2412_;
                }
            }
            1 => {
                if v_isShared_2406_ == 0 {
                    v___x_2408_ = v___x_2405_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2409_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_a_2403_);
                    v___x_2408_ = v_reuseFailAlloc_2409_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2408_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs___boxed(
    mut v_declName_2413_: *mut crate::leanh::LeanObject,
    mut v_args_2414_: *mut crate::leanh::LeanObject,
    mut v_a_2415_: *mut crate::leanh::LeanObject,
    mut v_a_2416_: *mut crate::leanh::LeanObject,
    mut v_a_2417_: *mut crate::leanh::LeanObject,
    mut v_a_2418_: *mut crate::leanh::LeanObject,
    mut v_a_2419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2420_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs(
        v_declName_2413_,
        v_args_2414_,
        v_a_2415_,
        v_a_2416_,
        v_a_2417_,
        v_a_2418_,
    );
    crate::leanh::lean_dec(v_a_2418_);
    crate::leanh::lean_dec_ref(v_a_2417_);
    crate::leanh::lean_dec(v_a_2416_);
    crate::leanh::lean_dec_ref(v_a_2415_);
    return v_res_2420_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0(
    mut v_sz_2421_: usize,
    mut v_i_2422_: usize,
    mut v_bs_2423_: *mut crate::leanh::LeanObject,
    mut v___y_2424_: *mut crate::leanh::LeanObject,
    mut v___y_2425_: *mut crate::leanh::LeanObject,
    mut v___y_2426_: *mut crate::leanh::LeanObject,
    mut v___y_2427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2429_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___redArg(v_sz_2421_, v_i_2422_, v_bs_2423_, v___y_2424_, v___y_2426_, v___y_2427_);
    return v___x_2429_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0___boxed(
    mut v_sz_2430_: *mut crate::leanh::LeanObject,
    mut v_i_2431_: *mut crate::leanh::LeanObject,
    mut v_bs_2432_: *mut crate::leanh::LeanObject,
    mut v___y_2433_: *mut crate::leanh::LeanObject,
    mut v___y_2434_: *mut crate::leanh::LeanObject,
    mut v___y_2435_: *mut crate::leanh::LeanObject,
    mut v___y_2436_: *mut crate::leanh::LeanObject,
    mut v___y_2437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2438_: usize = 0;
    let mut v_i_boxed_2439_: usize = 0;
    let mut v_res_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2438_ = crate::leanh::lean_unbox_usize(v_sz_2430_);
    crate::leanh::lean_dec(v_sz_2430_);
    v_i_boxed_2439_ = crate::leanh::lean_unbox_usize(v_i_2431_);
    crate::leanh::lean_dec(v_i_2431_);
    v_res_2440_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__0(v_sz_boxed_2438_, v_i_boxed_2439_, v_bs_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
    crate::leanh::lean_dec(v___y_2436_);
    crate::leanh::lean_dec_ref(v___y_2435_);
    crate::leanh::lean_dec(v___y_2434_);
    crate::leanh::lean_dec_ref(v___y_2433_);
    return v_res_2440_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2(
    mut v_00_u03b1_2441_: *mut crate::leanh::LeanObject,
    mut v_ref_2442_: *mut crate::leanh::LeanObject,
    mut v_msg_2443_: *mut crate::leanh::LeanObject,
    mut v___y_2444_: *mut crate::leanh::LeanObject,
    mut v___y_2445_: *mut crate::leanh::LeanObject,
    mut v___y_2446_: *mut crate::leanh::LeanObject,
    mut v___y_2447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2449_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___redArg(v_ref_2442_, v_msg_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
    return v___x_2449_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2___boxed(
    mut v_00_u03b1_2450_: *mut crate::leanh::LeanObject,
    mut v_ref_2451_: *mut crate::leanh::LeanObject,
    mut v_msg_2452_: *mut crate::leanh::LeanObject,
    mut v___y_2453_: *mut crate::leanh::LeanObject,
    mut v___y_2454_: *mut crate::leanh::LeanObject,
    mut v___y_2455_: *mut crate::leanh::LeanObject,
    mut v___y_2456_: *mut crate::leanh::LeanObject,
    mut v___y_2457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2458_ = l_Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2(v_00_u03b1_2450_, v_ref_2451_, v_msg_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
    crate::leanh::lean_dec(v___y_2456_);
    crate::leanh::lean_dec_ref(v___y_2455_);
    crate::leanh::lean_dec(v___y_2454_);
    crate::leanh::lean_dec_ref(v___y_2453_);
    crate::leanh::lean_dec(v_ref_2451_);
    return v_res_2458_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5(
    mut v_n_2459_: *mut crate::leanh::LeanObject,
    mut v_as_2460_: *mut crate::leanh::LeanObject,
    mut v_lo_2461_: *mut crate::leanh::LeanObject,
    mut v_hi_2462_: *mut crate::leanh::LeanObject,
    mut v_w_2463_: *mut crate::leanh::LeanObject,
    mut v_hlo_2464_: *mut crate::leanh::LeanObject,
    mut v_hhi_2465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2466_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___redArg(v_n_2459_, v_as_2460_, v_lo_2461_, v_hi_2462_);
    return v___x_2466_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5___boxed(
    mut v_n_2467_: *mut crate::leanh::LeanObject,
    mut v_as_2468_: *mut crate::leanh::LeanObject,
    mut v_lo_2469_: *mut crate::leanh::LeanObject,
    mut v_hi_2470_: *mut crate::leanh::LeanObject,
    mut v_w_2471_: *mut crate::leanh::LeanObject,
    mut v_hlo_2472_: *mut crate::leanh::LeanObject,
    mut v_hhi_2473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2474_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5(v_n_2467_, v_as_2468_, v_lo_2469_, v_hi_2470_, v_w_2471_, v_hlo_2472_, v_hhi_2473_);
    crate::leanh::lean_dec(v_hi_2470_);
    crate::leanh::lean_dec(v_n_2467_);
    return v_res_2474_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3(
    mut v_00_u03b1_2475_: *mut crate::leanh::LeanObject,
    mut v_msg_2476_: *mut crate::leanh::LeanObject,
    mut v___y_2477_: *mut crate::leanh::LeanObject,
    mut v___y_2478_: *mut crate::leanh::LeanObject,
    mut v___y_2479_: *mut crate::leanh::LeanObject,
    mut v___y_2480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2482_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___redArg(v_msg_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
    return v___x_2482_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3___boxed(
    mut v_00_u03b1_2483_: *mut crate::leanh::LeanObject,
    mut v_msg_2484_: *mut crate::leanh::LeanObject,
    mut v___y_2485_: *mut crate::leanh::LeanObject,
    mut v___y_2486_: *mut crate::leanh::LeanObject,
    mut v___y_2487_: *mut crate::leanh::LeanObject,
    mut v___y_2488_: *mut crate::leanh::LeanObject,
    mut v___y_2489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2490_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__2_spec__3(v_00_u03b1_2483_, v_msg_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
    crate::leanh::lean_dec(v___y_2488_);
    crate::leanh::lean_dec_ref(v___y_2487_);
    crate::leanh::lean_dec(v___y_2486_);
    crate::leanh::lean_dec_ref(v___y_2485_);
    return v_res_2490_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8(
    mut v_n_2491_: *mut crate::leanh::LeanObject,
    mut v_lo_2492_: *mut crate::leanh::LeanObject,
    mut v_hi_2493_: *mut crate::leanh::LeanObject,
    mut v_hhi_2494_: *mut crate::leanh::LeanObject,
    mut v_pivot_2495_: *mut crate::leanh::LeanObject,
    mut v_as_2496_: *mut crate::leanh::LeanObject,
    mut v_i_2497_: *mut crate::leanh::LeanObject,
    mut v_k_2498_: *mut crate::leanh::LeanObject,
    mut v_ilo_2499_: *mut crate::leanh::LeanObject,
    mut v_ik_2500_: *mut crate::leanh::LeanObject,
    mut v_w_2501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2502_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8___redArg(v_hi_2493_, v_pivot_2495_, v_as_2496_, v_i_2497_, v_k_2498_);
    return v___x_2502_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8___boxed(
    mut v_n_2503_: *mut crate::leanh::LeanObject,
    mut v_lo_2504_: *mut crate::leanh::LeanObject,
    mut v_hi_2505_: *mut crate::leanh::LeanObject,
    mut v_hhi_2506_: *mut crate::leanh::LeanObject,
    mut v_pivot_2507_: *mut crate::leanh::LeanObject,
    mut v_as_2508_: *mut crate::leanh::LeanObject,
    mut v_i_2509_: *mut crate::leanh::LeanObject,
    mut v_k_2510_: *mut crate::leanh::LeanObject,
    mut v_ilo_2511_: *mut crate::leanh::LeanObject,
    mut v_ik_2512_: *mut crate::leanh::LeanObject,
    mut v_w_2513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2514_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__5_spec__8(v_n_2503_, v_lo_2504_, v_hi_2505_, v_hhi_2506_, v_pivot_2507_, v_as_2508_, v_i_2509_, v_k_2510_, v_ilo_2511_, v_ik_2512_, v_w_2513_);
    crate::leanh::lean_dec(v_pivot_2507_);
    crate::leanh::lean_dec(v_hi_2505_);
    crate::leanh::lean_dec(v_lo_2504_);
    crate::leanh::lean_dec(v_n_2503_);
    return v_res_2514_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10(
    mut v_00_u03b1_2515_: *mut crate::leanh::LeanObject,
    mut v_constName_2516_: *mut crate::leanh::LeanObject,
    mut v___y_2517_: *mut crate::leanh::LeanObject,
    mut v___y_2518_: *mut crate::leanh::LeanObject,
    mut v___y_2519_: *mut crate::leanh::LeanObject,
    mut v___y_2520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2522_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10___redArg(v_constName_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
    return v___x_2522_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10___boxed(
    mut v_00_u03b1_2523_: *mut crate::leanh::LeanObject,
    mut v_constName_2524_: *mut crate::leanh::LeanObject,
    mut v___y_2525_: *mut crate::leanh::LeanObject,
    mut v___y_2526_: *mut crate::leanh::LeanObject,
    mut v___y_2527_: *mut crate::leanh::LeanObject,
    mut v___y_2528_: *mut crate::leanh::LeanObject,
    mut v___y_2529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2530_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10(v_00_u03b1_2523_, v_constName_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
    crate::leanh::lean_dec(v___y_2528_);
    crate::leanh::lean_dec_ref(v___y_2527_);
    crate::leanh::lean_dec(v___y_2526_);
    crate::leanh::lean_dec_ref(v___y_2525_);
    return v_res_2530_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14(
    mut v_00_u03b1_2531_: *mut crate::leanh::LeanObject,
    mut v_ref_2532_: *mut crate::leanh::LeanObject,
    mut v_constName_2533_: *mut crate::leanh::LeanObject,
    mut v___y_2534_: *mut crate::leanh::LeanObject,
    mut v___y_2535_: *mut crate::leanh::LeanObject,
    mut v___y_2536_: *mut crate::leanh::LeanObject,
    mut v___y_2537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2539_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___redArg(v_ref_2532_, v_constName_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
    return v___x_2539_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14___boxed(
    mut v_00_u03b1_2540_: *mut crate::leanh::LeanObject,
    mut v_ref_2541_: *mut crate::leanh::LeanObject,
    mut v_constName_2542_: *mut crate::leanh::LeanObject,
    mut v___y_2543_: *mut crate::leanh::LeanObject,
    mut v___y_2544_: *mut crate::leanh::LeanObject,
    mut v___y_2545_: *mut crate::leanh::LeanObject,
    mut v___y_2546_: *mut crate::leanh::LeanObject,
    mut v___y_2547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2548_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14(v_00_u03b1_2540_, v_ref_2541_, v_constName_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
    crate::leanh::lean_dec(v___y_2546_);
    crate::leanh::lean_dec_ref(v___y_2545_);
    crate::leanh::lean_dec(v___y_2544_);
    crate::leanh::lean_dec_ref(v___y_2543_);
    crate::leanh::lean_dec(v_ref_2541_);
    return v_res_2548_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15(
    mut v_00_u03b1_2549_: *mut crate::leanh::LeanObject,
    mut v_ref_2550_: *mut crate::leanh::LeanObject,
    mut v_msg_2551_: *mut crate::leanh::LeanObject,
    mut v_declHint_2552_: *mut crate::leanh::LeanObject,
    mut v___y_2553_: *mut crate::leanh::LeanObject,
    mut v___y_2554_: *mut crate::leanh::LeanObject,
    mut v___y_2555_: *mut crate::leanh::LeanObject,
    mut v___y_2556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2558_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15___redArg(v_ref_2550_, v_msg_2551_, v_declHint_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
    return v___x_2558_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15___boxed(
    mut v_00_u03b1_2559_: *mut crate::leanh::LeanObject,
    mut v_ref_2560_: *mut crate::leanh::LeanObject,
    mut v_msg_2561_: *mut crate::leanh::LeanObject,
    mut v_declHint_2562_: *mut crate::leanh::LeanObject,
    mut v___y_2563_: *mut crate::leanh::LeanObject,
    mut v___y_2564_: *mut crate::leanh::LeanObject,
    mut v___y_2565_: *mut crate::leanh::LeanObject,
    mut v___y_2566_: *mut crate::leanh::LeanObject,
    mut v___y_2567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2568_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15(v_00_u03b1_2559_, v_ref_2560_, v_msg_2561_, v_declHint_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
    crate::leanh::lean_dec(v___y_2566_);
    crate::leanh::lean_dec_ref(v___y_2565_);
    crate::leanh::lean_dec(v___y_2564_);
    crate::leanh::lean_dec_ref(v___y_2563_);
    crate::leanh::lean_dec(v_ref_2560_);
    return v_res_2568_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17(
    mut v_msg_2569_: *mut crate::leanh::LeanObject,
    mut v_declHint_2570_: *mut crate::leanh::LeanObject,
    mut v___y_2571_: *mut crate::leanh::LeanObject,
    mut v___y_2572_: *mut crate::leanh::LeanObject,
    mut v___y_2573_: *mut crate::leanh::LeanObject,
    mut v___y_2574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2576_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg(v_msg_2569_, v_declHint_2570_, v___y_2574_);
    return v___x_2576_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___boxed(
    mut v_msg_2577_: *mut crate::leanh::LeanObject,
    mut v_declHint_2578_: *mut crate::leanh::LeanObject,
    mut v___y_2579_: *mut crate::leanh::LeanObject,
    mut v___y_2580_: *mut crate::leanh::LeanObject,
    mut v___y_2581_: *mut crate::leanh::LeanObject,
    mut v___y_2582_: *mut crate::leanh::LeanObject,
    mut v___y_2583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2584_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17(v_msg_2577_, v_declHint_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
    crate::leanh::lean_dec(v___y_2582_);
    crate::leanh::lean_dec_ref(v___y_2581_);
    crate::leanh::lean_dec(v___y_2580_);
    crate::leanh::lean_dec_ref(v___y_2579_);
    return v_res_2584_;
}
pub unsafe fn l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(
    mut v_x_2585_: *mut crate::leanh::LeanObject,
    mut v_x_2586_: *mut crate::leanh::LeanObject,
    mut v_x_2587_: *mut crate::leanh::LeanObject,
    mut v___y_2588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2590_ = crate::leanh::lean_box(0);
    v___x_2591_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2591_, 0, v___x_2590_);
    return v___x_2591_;
}
pub unsafe fn l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed(
    mut v_x_2592_: *mut crate::leanh::LeanObject,
    mut v_x_2593_: *mut crate::leanh::LeanObject,
    mut v_x_2594_: *mut crate::leanh::LeanObject,
    mut v___y_2595_: *mut crate::leanh::LeanObject,
    mut v___y_2596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2597_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(v_x_2592_, v_x_2593_, v_x_2594_, v___y_2595_);
    crate::leanh::lean_dec(v___y_2595_);
    crate::leanh::lean_dec_ref(v_x_2594_);
    crate::leanh::lean_dec_ref(v_x_2593_);
    crate::leanh::lean_dec(v_x_2592_);
    return v_res_2597_;
}
pub unsafe fn _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_()
-> u64 {
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: u64 = 0;
    v___x_2604_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_;
    v___x_2605_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2604_);
    return v___x_2605_;
}
pub unsafe fn _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2606_: u64 = 0;
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2606_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
    v___x_2607_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__0_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_;
    v___x_2608_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
    crate::leanh::lean_ctor_set(v___x_2608_, 0, v___x_2607_);
    crate::leanh::lean_ctor_set_uint64(
        v___x_2608_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2606_,
    );
    return v___x_2608_;
}
pub unsafe fn _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2609_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2609_;
}
pub unsafe fn _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2610_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
    v___x_2611_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2611_, 0, v___x_2610_);
    return v___x_2611_;
}
pub unsafe fn _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2612_ = crate::leanh::lean_box(1);
    v___x_2613_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4);
    v___x_2614_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
    v___x_2615_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2615_, 0, v___x_2614_);
    crate::leanh::lean_ctor_set(v___x_2615_, 1, v___x_2613_);
    crate::leanh::lean_ctor_set(v___x_2615_, 2, v___x_2612_);
    return v___x_2615_;
}
pub unsafe fn _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2618_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
    v___x_2619_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2620_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2620_, 0, v___x_2619_);
    crate::leanh::lean_ctor_set(v___x_2620_, 1, v___x_2619_);
    crate::leanh::lean_ctor_set(v___x_2620_, 2, v___x_2619_);
    crate::leanh::lean_ctor_set(v___x_2620_, 3, v___x_2619_);
    crate::leanh::lean_ctor_set(v___x_2620_, 4, v___x_2618_);
    crate::leanh::lean_ctor_set(v___x_2620_, 5, v___x_2618_);
    crate::leanh::lean_ctor_set(v___x_2620_, 6, v___x_2618_);
    crate::leanh::lean_ctor_set(v___x_2620_, 7, v___x_2618_);
    crate::leanh::lean_ctor_set(v___x_2620_, 8, v___x_2618_);
    crate::leanh::lean_ctor_set(v___x_2620_, 9, v___x_2618_);
    return v___x_2620_;
}
pub unsafe fn _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2621_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
    v___x_2622_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2622_, 0, v___x_2621_);
    crate::leanh::lean_ctor_set(v___x_2622_, 1, v___x_2621_);
    crate::leanh::lean_ctor_set(v___x_2622_, 2, v___x_2621_);
    crate::leanh::lean_ctor_set(v___x_2622_, 3, v___x_2621_);
    crate::leanh::lean_ctor_set(v___x_2622_, 4, v___x_2621_);
    crate::leanh::lean_ctor_set(v___x_2622_, 5, v___x_2621_);
    return v___x_2622_;
}
pub unsafe fn _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__9_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2623_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
    v___x_2624_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2624_, 0, v___x_2623_);
    crate::leanh::lean_ctor_set(v___x_2624_, 1, v___x_2623_);
    crate::leanh::lean_ctor_set(v___x_2624_, 2, v___x_2623_);
    crate::leanh::lean_ctor_set(v___x_2624_, 3, v___x_2623_);
    crate::leanh::lean_ctor_set(v___x_2624_, 4, v___x_2623_);
    return v___x_2624_;
}
pub unsafe fn l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(
    mut v___x_2625_: *mut crate::leanh::LeanObject,
    mut v_declName_2626_: *mut crate::leanh::LeanObject,
    mut v_stx_2627_: *mut crate::leanh::LeanObject,
    mut v___y_2628_: *mut crate::leanh::LeanObject,
    mut v___y_2629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2631_: u8 = 0;
    let mut v___x_2632_: u8 = 0;
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2652_: u8 = 0;
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2657_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2631_ = 0;
                v___x_2632_ = 1;
                v___x_2633_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
                v___x_2634_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2635_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs_spec__6_spec__10_spec__14_spec__15_spec__16_spec__17___redArg___closed__4);
                v___x_2636_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__5_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
                v___x_2637_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__6_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_;
                v___x_2638_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v___x_2625_);
                v___x_2639_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_2639_, 0, v___x_2633_);
                crate::leanh::lean_ctor_set(v___x_2639_, 1, v___x_2625_);
                crate::leanh::lean_ctor_set(v___x_2639_, 2, v___x_2636_);
                crate::leanh::lean_ctor_set(v___x_2639_, 3, v___x_2637_);
                crate::leanh::lean_ctor_set(v___x_2639_, 4, v___x_2638_);
                crate::leanh::lean_ctor_set(v___x_2639_, 5, v___x_2634_);
                crate::leanh::lean_ctor_set(v___x_2639_, 6, v___x_2638_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2639_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v___x_2631_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2639_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v___x_2631_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2639_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v___x_2631_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2639_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v___x_2632_,
                );
                v___x_2640_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__7_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
                v___x_2641_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__8_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
                v___x_2642_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__9_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__9_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1___closed__9_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_);
                v___x_2643_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2643_, 0, v___x_2640_);
                crate::leanh::lean_ctor_set(v___x_2643_, 1, v___x_2641_);
                crate::leanh::lean_ctor_set(v___x_2643_, 2, v___x_2625_);
                crate::leanh::lean_ctor_set(v___x_2643_, 3, v___x_2635_);
                crate::leanh::lean_ctor_set(v___x_2643_, 4, v___x_2642_);
                v___x_2644_ = lean_st_mk_ref(v___x_2643_);
                v___x_2645_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2646_ = l_Lean_Syntax_getArg(v_stx_2627_, v___x_2645_);
                v_args_2647_ = l_Lean_Syntax_getArgs(v___x_2646_);
                crate::leanh::lean_dec(v___x_2646_);
                v___x_2648_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_elabSpecArgs(
                    v_declName_2626_,
                    v_args_2647_,
                    v___x_2639_,
                    v___x_2644_,
                    v___y_2628_,
                    v___y_2629_,
                );
                crate::leanh::lean_dec_ref_known(v___x_2639_, 7);
                if crate::leanh::lean_obj_tag(v___x_2648_) == 0 {
                    v_a_2649_ = crate::leanh::lean_ctor_get(v___x_2648_, 0);
                    v_isSharedCheck_2657_ = (!crate::leanh::lean_is_exclusive(v___x_2648_)) as u8;
                    if v_isSharedCheck_2657_ == 0 {
                        v___x_2651_ = v___x_2648_;
                        v_isShared_2652_ = v_isSharedCheck_2657_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2649_);
                        crate::leanh::lean_dec(v___x_2648_);
                        v___x_2651_ = crate::leanh::lean_box(0);
                        v_isShared_2652_ = v_isSharedCheck_2657_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2644_);
                    return v___x_2648_;
                }
            }
            1 => {
                v___x_2653_ = lean_st_ref_get(v___x_2644_);
                crate::leanh::lean_dec(v___x_2644_);
                crate::leanh::lean_dec(v___x_2653_);
                if v_isShared_2652_ == 0 {
                    v___x_2655_ = v___x_2651_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2656_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_a_2649_);
                    v___x_2655_ = v_reuseFailAlloc_2656_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2655_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed(
    mut v___x_2658_: *mut crate::leanh::LeanObject,
    mut v_declName_2659_: *mut crate::leanh::LeanObject,
    mut v_stx_2660_: *mut crate::leanh::LeanObject,
    mut v___y_2661_: *mut crate::leanh::LeanObject,
    mut v___y_2662_: *mut crate::leanh::LeanObject,
    mut v___y_2663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2664_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(v___x_2658_, v_declName_2659_, v_stx_2660_, v___y_2661_, v___y_2662_);
    crate::leanh::lean_dec(v___y_2662_);
    crate::leanh::lean_dec_ref(v___y_2661_);
    crate::leanh::lean_dec(v_stx_2660_);
    return v_res_2664_;
}
pub unsafe fn l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(
    mut v___x_2665_: u8,
    mut v_env_2666_: *mut crate::leanh::LeanObject,
    mut v_n_2667_: *mut crate::leanh::LeanObject,
    mut v_x_2668_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2669_: u8 = 0;
    v___x_2669_ = l_Lean_Environment_contains(v_env_2666_, v_n_2667_, v___x_2665_);
    return v___x_2669_;
}
pub unsafe fn l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed(
    mut v___x_2670_: *mut crate::leanh::LeanObject,
    mut v_env_2671_: *mut crate::leanh::LeanObject,
    mut v_n_2672_: *mut crate::leanh::LeanObject,
    mut v_x_2673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_553__boxed_2674_: u8 = 0;
    let mut v_res_2675_: u8 = 0;
    let mut v_r_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_553__boxed_2674_ = (crate::leanh::lean_unbox(v___x_2670_) as u8);
    v_res_2675_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___lam__2_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_(v___x_553__boxed_2674_, v_env_2671_, v_n_2672_, v_x_2673_);
    crate::leanh::lean_dec_ref(v_x_2673_);
    v_r_2676_ = crate::leanh::lean_box((v_res_2675_) as usize);
    return v_r_2676_;
}
pub unsafe fn l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2704_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_;
    v___x_2705_ = l_Lean_registerParametricAttribute___redArg(v___x_2704_);
    return v___x_2705_;
}
pub unsafe fn l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2____boxed(
    mut v_a_2706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2707_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_();
    return v_res_2707_;
}
pub unsafe fn l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2710_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_;
    v___x_2711_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1___closed__0;
    v___x_2712_ = l_Lean_addBuiltinDocString(v___x_2710_, v___x_2711_);
    return v___x_2712_;
}
pub unsafe fn l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1___boxed(
    mut v_a_2713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2714_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1();
    return v_res_2714_;
}
pub unsafe fn l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2741_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_;
    v___x_2742_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___closed__6;
    v___x_2743_ = l_Lean_addBuiltinDeclarationRanges(v___x_2741_, v___x_2742_);
    return v___x_2743_;
}
pub unsafe fn l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3___boxed(
    mut v_a_2744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2745_ = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3();
    return v_res_2745_;
}
pub unsafe fn _init_l_Lean_Compiler_getSpecializationArgs_x3f___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2746_ = l_Array_instInhabited(crate::leanh::lean_box(0));
    return v___x_2746_;
}
pub unsafe fn l_Lean_Compiler_getSpecializationArgs_x3f(
    mut v_env_2747_: *mut crate::leanh::LeanObject,
    mut v_declName_2748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2749_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_getSpecializationArgs_x3f___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_getSpecializationArgs_x3f___closed__0_once),
        _init_l_Lean_Compiler_getSpecializationArgs_x3f___closed__0,
    );
    v___x_2750_ = l_Lean_Compiler_specializeAttr;
    v___x_2751_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(
        v___x_2749_,
        v___x_2750_,
        v_env_2747_,
        v_declName_2748_,
    );
    return v___x_2751_;
}
pub unsafe fn l_Lean_Compiler_hasSpecializeAttribute(
    mut v_env_2752_: *mut crate::leanh::LeanObject,
    mut v_declName_2753_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2754_ = l_Lean_Compiler_getSpecializationArgs_x3f(v_env_2752_, v_declName_2753_);
    if crate::leanh::lean_obj_tag(v___x_2754_) == 0 {
        let mut v___x_2755_: u8 = 0;
        v___x_2755_ = 0;
        return v___x_2755_;
    } else {
        let mut v___x_2756_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_2754_, 1);
        v___x_2756_ = 1;
        return v___x_2756_;
    }
}
pub unsafe fn l_Lean_Compiler_hasSpecializeAttribute___boxed(
    mut v_env_2757_: *mut crate::leanh::LeanObject,
    mut v_declName_2758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2759_: u8 = 0;
    let mut v_r_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2759_ = l_Lean_Compiler_hasSpecializeAttribute(v_env_2757_, v_declName_2758_);
    v_r_2760_ = crate::leanh::lean_box((v_res_2759_) as usize);
    return v_r_2760_;
}
pub unsafe fn l_Lean_Compiler_hasNospecializeAttribute(
    mut v_env_2761_: *mut crate::leanh::LeanObject,
    mut v_declName_2762_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: u8 = 0;
    v___x_2763_ = l_Lean_Compiler_nospecializeAttr;
    v___x_2764_ = l_Lean_TagAttribute_hasTag(v___x_2763_, v_env_2761_, v_declName_2762_);
    return v___x_2764_;
}
pub unsafe fn l_Lean_Compiler_hasNospecializeAttribute___boxed(
    mut v_env_2765_: *mut crate::leanh::LeanObject,
    mut v_declName_2766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2767_: u8 = 0;
    let mut v_r_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2767_ = l_Lean_Compiler_hasNospecializeAttribute(v_env_2765_, v_declName_2766_);
    v_r_2768_ = crate::leanh::lean_box((v_res_2767_) as usize);
    return v_r_2768_;
}
pub unsafe fn l_Lean_Compiler_hasWeakSpecializeAttribute(
    mut v_env_2769_: *mut crate::leanh::LeanObject,
    mut v_declName_2770_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: u8 = 0;
    v___x_2771_ = l_Lean_Compiler_weakSpecializeAttr;
    v___x_2772_ = l_Lean_TagAttribute_hasTag(v___x_2771_, v_env_2769_, v_declName_2770_);
    return v___x_2772_;
}
pub unsafe fn l_Lean_Compiler_hasWeakSpecializeAttribute___boxed(
    mut v_env_2773_: *mut crate::leanh::LeanObject,
    mut v_declName_2774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2775_: u8 = 0;
    let mut v_r_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2775_ = l_Lean_Compiler_hasWeakSpecializeAttribute(v_env_2773_, v_declName_2774_);
    v_r_2776_ = crate::leanh::lean_box((v_res_2775_) as usize);
    return v_r_2776_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_Specialize(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Compiler_instInhabitedSpecializeAttributeKind_default =
        _init_l_Lean_Compiler_instInhabitedSpecializeAttributeKind_default();
    l_Lean_Compiler_instInhabitedSpecializeAttributeKind =
        _init_l_Lean_Compiler_instInhabitedSpecializeAttributeKind();
    res = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_250634751____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_nospecializeAttr = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Compiler_nospecializeAttr);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_docString__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_nospecializeAttr___regBuiltin_Lean_Compiler_nospecializeAttr_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_1607742496____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_weakSpecializeAttr = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Compiler_weakSpecializeAttr);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_docString__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_weakSpecializeAttr___regBuiltin_Lean_Compiler_weakSpecializeAttr_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Specialize_149776412____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_specializeAttr = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Compiler_specializeAttr);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_docString__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_specializeAttr___regBuiltin_Lean_Compiler_specializeAttr_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_Specialize(
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
pub unsafe fn initialize_Lean_Compiler_Specialize(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_Specialize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_Specialize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_Specialize(builtin);
}
