// Lean compiler output
// Module: Lean.Server.CodeActions.Attr
// Imports: Lean.Server.CodeActions.Basic Lean.Compiler.IR.CompilerM
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed,
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_num___override,
    l_Lean_Name_str___override, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs,
    l_Lean_Syntax_isOfKind,
};
use crate::r#gen::Init::System::IOError::{lean_io_error_to_string, lean_mk_io_user_error};
use crate::r#gen::Lean::Attributes::{
    l_Lean_Attribute_Builtin_ensureNoArgs, l_Lean_ensureAttrDeclIsMeta,
    l_Lean_instBEqAttributeKind_beq, l_Lean_registerBuiltinAttribute,
};
use crate::r#gen::Lean::Compiler::IR::CompilerM::{
    initialize_Lean_Compiler_IR_CompilerM, lean_decl_get_sorry_dep,
    runtime_initialize_Lean_Compiler_IR_CompilerM,
};
use crate::r#gen::Lean::Compiler::InitAttr::l_Lean_declareBuiltin;
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_isMarkedMeta;
use crate::r#gen::Lean::CoreM::l_Lean_Core_mkFreshUserName;
use crate::r#gen::Lean::Data::Name::{
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl, l_Lean_Name_isAnonymous,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_empty, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Elab::InfoTree::Main::l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo;
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_evalConstCheck___redArg, l_Lean_Environment_getModuleIdxFor_x3f,
    l_Lean_Environment_header, l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_instInhabitedEffectiveImport_default,
    l_Lean_registerPersistentEnvExtensionUnsafe___redArg,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_mkAppB, l_Lean_mkAppN, l_Lean_mkConst,
};
use crate::r#gen::Lean::ExtraModUses::{
    l___private_Lean_ExtraModUses_0__Lean_extraModUses, l_Lean_indirectModUseExt,
    l_Lean_instBEqExtraModUse_beq, l_Lean_instBEqExtraModUse_beq___boxed,
    l_Lean_instHashableExtraModUse_hash, l_Lean_instHashableExtraModUse_hash___boxed,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Server::CodeActions::Basic::{
    initialize_Lean_Server_CodeActions_Basic, runtime_initialize_Lean_Server_CodeActions_Basic,
};
use crate::r#gen::Lean::ToExpr::l___private_Lean_ToExpr_0__Lean_Name_toExprAux;
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::r#gen::Std::Data::HashMap::Basic::l_Std_HashMap_instInhabited;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__1_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__2_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [72, 111, 108, 101, 67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__1_value) as *mut crate::leanh::LeanObject,1630946840184265901 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__2_value) as *mut crate::leanh::LeanObject,15336260586967034768 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__2_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__3_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [104, 111, 108, 101, 67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 69, 120, 116, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__1_value) as *mut crate::leanh::LeanObject,1630946840184265901 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18169146760106986306 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__4_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 3, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<8> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*8 + 0) as u16, other: 8, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__11_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__11_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__11_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_CodeAction_holeCodeActionExt: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 115, 99, 111, 112, 101, 58, 32, 65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__2_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [93, 96, 32, 109, 117, 115, 116, 32, 98, 101, 32, 103, 108, 111, 98, 97, 108, 44, 32, 110, 111, 116, 32, 96, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__4_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__6_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [103, 108, 111, 98, 97, 108, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 111, 99, 97, 108, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__8_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 99, 111, 112, 101, 100, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 101, 114, 118, 101, 114, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12337524736695414095 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17302608593553616169 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [65, 116, 116, 114, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9914264936907428297 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,1208168756163512716 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value) as *mut crate::leanh::LeanObject,12060895093625083661 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__11_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__1_value) as *mut crate::leanh::LeanObject,4737180066981367002 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__11_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__11_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__12_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__12_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__12_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__13_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__11_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__12_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11048415496356105535 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__13_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__13_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__14_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__14_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__14_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__15_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__13_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__14_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5775873084443761098 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__15_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__15_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__16_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__15_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value) as *mut crate::leanh::LeanObject,16657014704763504075 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__16_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__16_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__17_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__16_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9546742709096449002 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__17_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__17_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__18_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__17_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10111873537814351968 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__18_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__18_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__19_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__18_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2580783235213447324 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__19_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__19_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__20_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__19_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 1824323934 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,13153020436653296944 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__20_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__20_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__21_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__21_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__21_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__22_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__20_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__21_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18209967886157034215 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__22_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__22_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__23_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__23_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__23_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__24_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__22_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__23_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11163147854334231087 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__24_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__24_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__25_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__24_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,18019106402232835370 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__25_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__25_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__26_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [104, 111, 108, 101, 95, 99, 111, 100, 101, 95, 97, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__26_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__26_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__27_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__26_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11443572138440657403 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__27_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__27_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__28_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 8, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__27_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__28_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__28_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__29_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__27_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__29_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__29_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__30_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<74> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 74, m_capacity: 74, m_length: 73, m_data: [68, 101, 99, 108, 97, 114, 101, 32, 97, 32, 110, 101, 119, 32, 104, 111, 108, 101, 32, 99, 111, 100, 101, 32, 97, 99, 116, 105, 111, 110, 44, 32, 116, 111, 32, 97, 112, 112, 101, 97, 114, 32, 105, 110, 32, 116, 104, 101, 32, 99, 111, 100, 101, 32, 97, 99, 116, 105, 111, 110, 115, 32, 111, 110, 32, 63, 95, 32, 97, 110, 100, 32, 95, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__30_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__30_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__31_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__25_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__27_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__30_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__31_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__31_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__32_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__31_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__28_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__29_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__32_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__32_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__0_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [67, 111, 109, 109, 97, 110, 100, 67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__1_value) as *mut crate::leanh::LeanObject,1630946840184265901 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__0_value) as *mut crate::leanh::LeanObject,15207379896936780160 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_CodeAction_instInhabitedCommandCodeActionEntry_default___closed__0_value:
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
static mut l_Lean_CodeAction_instInhabitedCommandCodeActionEntry_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_CodeAction_instInhabitedCommandCodeActionEntry_default___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_CodeAction_instInhabitedCommandCodeActionEntry_default___closed__1_value:
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
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_CodeAction_instInhabitedCommandCodeActionEntry_default___closed__0_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_CodeAction_instInhabitedCommandCodeActionEntry_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_CodeAction_instInhabitedCommandCodeActionEntry_default___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_CodeAction_instInhabitedCommandCodeActionEntry_default:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_CodeAction_instInhabitedCommandCodeActionEntry_default___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_CodeAction_instInhabitedCommandCodeActionEntry:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_CodeAction_instInhabitedCommandCodeActionEntry_default___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_CodeAction_instInhabitedCommandCodeActions_default___closed__0_value:
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
static mut l_Lean_CodeAction_instInhabitedCommandCodeActions_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_CodeAction_instInhabitedCommandCodeActions_default___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_CodeAction_instInhabitedCommandCodeActions_default___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_CodeAction_instInhabitedCommandCodeActions_default___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_CodeAction_instInhabitedCommandCodeActions_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_CodeAction_instInhabitedCommandCodeActions_default___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_CodeAction_instInhabitedCommandCodeActions_default:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_CodeAction_instInhabitedCommandCodeActions_default___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_CodeAction_instInhabitedCommandCodeActions: *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_CodeAction_instInhabitedCommandCodeActions_default___closed__1_value
)
    as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_CommandCodeActions_insert_spec__1___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_CommandCodeActions_insert_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_CommandCodeActions_insert_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_CodeAction_builtinCmdCodeActions: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__4___closed__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__4___closed__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__4___closed__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__2_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__3_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [99, 109, 100, 67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 69, 120, 116, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__1_value) as *mut crate::leanh::LeanObject,1630946840184265901 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7373477140738405138 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_CodeAction_cmdCodeActionExt: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__1: usize = 0;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__3_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__3_value) as *mut crate::leanh::LeanObject,7870113334857981723 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__5_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__7_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__10_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__10_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__13_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__13_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__14: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__15_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__15_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__16_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__16: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__17_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__18_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__19_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__20_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__20_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg___closed__0: u64 = 0;
pub static l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__3_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__19_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 249496773 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,10279444048633815591 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__21_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17778551580831994572 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__23_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3334465087617531768 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,17246597584702003577 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [99, 111, 109, 109, 97, 110, 100, 95, 99, 111, 100, 101, 95, 97, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2488340241968920392 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<5> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*5) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 5, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<77> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 77, m_capacity: 77, m_length: 76, m_data: [68, 101, 99, 108, 97, 114, 101, 32, 97, 32, 110, 101, 119, 32, 99, 111, 109, 109, 97, 110, 100, 32, 99, 111, 100, 101, 32, 97, 99, 116, 105, 111, 110, 44, 32, 116, 111, 32, 97, 112, 112, 101, 97, 114, 32, 105, 110, 32, 116, 104, 101, 32, 99, 111, 100, 101, 32, 97, 99, 116, 105, 111, 110, 115, 32, 111, 110, 32, 99, 111, 109, 109, 97, 110, 100, 115, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__0_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [105, 110, 115, 101, 114, 116, 66, 117, 105, 108, 116, 105, 110, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__0_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__1_value) as *mut crate::leanh::LeanObject,1630946840184265901 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__0_value) as *mut crate::leanh::LeanObject,14351884860939696436 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [78, 97, 109, 101, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__3_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__3_value) as *mut crate::leanh::LeanObject,13306843946249674491 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__4_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__6_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 105, 115, 116, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__7_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 111, 65, 114, 114, 97, 121, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__7_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__6_value) as *mut crate::leanh::LeanObject,9582258842178272501 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__7_value) as *mut crate::leanh::LeanObject,8414467900391110369 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__9_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__9_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__16_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 101, 99, 108, 97, 114, 101, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__16_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__16_value) as *mut crate::leanh::LeanObject,13812150225987229964 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__17_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__18_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 105, 108, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__18_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__19_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__6_value) as *mut crate::leanh::LeanObject,9582258842178272501 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__19_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__19_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__18_value) as *mut crate::leanh::LeanObject,18135193680607614554 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__19_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__20_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__21_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__22_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 111, 110, 115, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__22_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__23_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__6_value) as *mut crate::leanh::LeanObject,9582258842178272501 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__23_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__23_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__22_value) as *mut crate::leanh::LeanObject,8614124190858717794 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__23_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__24_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__25_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<50> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 50, m_capacity: 50, m_length: 49, m_data: [85, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 96, 99, 111, 109, 109, 97, 110, 100, 95, 99, 111, 100, 101, 95, 97, 99, 116, 105, 111, 110, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 115, 121, 110, 116, 97, 120, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__19_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 1324802641 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,9807269913042915022 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__21_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4616878115496534297 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__23_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3983418355711173073 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,14323203857448747948 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 99, 111, 109, 109, 97, 110, 100, 95, 99, 111, 100, 101, 95, 97, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<2> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 8, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5096520196538450623 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<85> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 85, m_capacity: 85, m_length: 84, m_data: [68, 101, 99, 108, 97, 114, 101, 32, 97, 32, 110, 101, 119, 32, 98, 117, 105, 108, 116, 105, 110, 32, 99, 111, 109, 109, 97, 110, 100, 32, 99, 111, 100, 101, 32, 97, 99, 116, 105, 111, 110, 44, 32, 116, 111, 32, 97, 112, 112, 101, 97, 114, 32, 105, 110, 32, 116, 104, 101, 32, 99, 111, 100, 101, 32, 97, 99, 116, 105, 111, 110, 115, 32, 111, 110, 32, 99, 111, 109, 109, 97, 110, 100, 115, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1(
    mut v_n_1809_: *mut crate::leanh::LeanObject,
    mut v_env_1810_: *mut crate::leanh::LeanObject,
    mut v_opts_1811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1812_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__3;
    v___x_1813_ = l_Lean_Environment_evalConstCheck___redArg(
        v_env_1810_,
        v_opts_1811_,
        v___x_1812_,
        v_n_1809_,
    );
    return v___x_1813_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___boxed(
    mut v_n_1814_: *mut crate::leanh::LeanObject,
    mut v_env_1815_: *mut crate::leanh::LeanObject,
    mut v_opts_1816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1817_ =
        l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1(
            v_n_1814_,
            v_env_1815_,
            v_opts_1816_,
        );
    crate::leanh::lean_dec_ref(v_opts_1816_);
    return v_res_1817_;
}
pub unsafe fn l_IO_ofExcept___at___00Lean_CodeAction_mkHoleCodeAction_spec__0___redArg(
    mut v_e_1818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1823_: u8 = 0;
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1828_: u8 = 0;
    let mut v_a_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1832_: u8 = 0;
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1836_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_1818_) == 0 {
                    v_a_1820_ = crate::leanh::lean_ctor_get(v_e_1818_, 0);
                    v_isSharedCheck_1828_ = (!crate::leanh::lean_is_exclusive(v_e_1818_)) as u8;
                    if v_isSharedCheck_1828_ == 0 {
                        v___x_1822_ = v_e_1818_;
                        v_isShared_1823_ = v_isSharedCheck_1828_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1820_);
                        crate::leanh::lean_dec(v_e_1818_);
                        v___x_1822_ = crate::leanh::lean_box(0);
                        v_isShared_1823_ = v_isSharedCheck_1828_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1829_ = crate::leanh::lean_ctor_get(v_e_1818_, 0);
                    v_isSharedCheck_1836_ = (!crate::leanh::lean_is_exclusive(v_e_1818_)) as u8;
                    if v_isSharedCheck_1836_ == 0 {
                        v___x_1831_ = v_e_1818_;
                        v_isShared_1832_ = v_isSharedCheck_1836_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1829_);
                        crate::leanh::lean_dec(v_e_1818_);
                        v___x_1831_ = crate::leanh::lean_box(0);
                        v_isShared_1832_ = v_isSharedCheck_1836_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1824_ = lean_mk_io_user_error(v_a_1820_);
                if v_isShared_1823_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1822_, 1);
                    crate::leanh::lean_ctor_set(v___x_1822_, 0, v___x_1824_);
                    v___x_1826_ = v___x_1822_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1827_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1824_);
                    v___x_1826_ = v_reuseFailAlloc_1827_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1826_;
            }
            3 => {
                if v_isShared_1832_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1831_, 0);
                    v___x_1834_ = v___x_1831_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1835_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1829_);
                    v___x_1834_ = v_reuseFailAlloc_1835_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1834_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_ofExcept___at___00Lean_CodeAction_mkHoleCodeAction_spec__0___redArg___boxed(
    mut v_e_1837_: *mut crate::leanh::LeanObject,
    mut v_a_1838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1839_ =
        l_IO_ofExcept___at___00Lean_CodeAction_mkHoleCodeAction_spec__0___redArg(v_e_1837_);
    return v_res_1839_;
}
pub unsafe fn l_IO_ofExcept___at___00Lean_CodeAction_mkHoleCodeAction_spec__0(
    mut v_00_u03b1_1840_: *mut crate::leanh::LeanObject,
    mut v_e_1841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1843_ =
        l_IO_ofExcept___at___00Lean_CodeAction_mkHoleCodeAction_spec__0___redArg(v_e_1841_);
    return v___x_1843_;
}
pub unsafe fn l_IO_ofExcept___at___00Lean_CodeAction_mkHoleCodeAction_spec__0___boxed(
    mut v_00_u03b1_1844_: *mut crate::leanh::LeanObject,
    mut v_e_1845_: *mut crate::leanh::LeanObject,
    mut v_a_1846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1847_ = l_IO_ofExcept___at___00Lean_CodeAction_mkHoleCodeAction_spec__0(
        v_00_u03b1_1844_,
        v_e_1845_,
    );
    return v_res_1847_;
}
pub unsafe fn l_Lean_CodeAction_mkHoleCodeAction(
    mut v_n_1848_: *mut crate::leanh::LeanObject,
    mut v_a_1849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_env_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_env_1851_ = crate::leanh::lean_ctor_get(v_a_1849_, 0);
    v_opts_1852_ = crate::leanh::lean_ctor_get(v_a_1849_, 1);
    crate::leanh::lean_inc_ref(v_env_1851_);
    v___x_1853_ =
        l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1(
            v_n_1848_,
            v_env_1851_,
            v_opts_1852_,
        );
    v___x_1854_ =
        l_IO_ofExcept___at___00Lean_CodeAction_mkHoleCodeAction_spec__0___redArg(v___x_1853_);
    return v___x_1854_;
}
pub unsafe fn l_Lean_CodeAction_mkHoleCodeAction___boxed(
    mut v_n_1855_: *mut crate::leanh::LeanObject,
    mut v_a_1856_: *mut crate::leanh::LeanObject,
    mut v_a_1857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1858_ = l_Lean_CodeAction_mkHoleCodeAction(v_n_1855_, v_a_1856_);
    crate::leanh::lean_dec_ref(v_a_1856_);
    return v_res_1858_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(
    mut v_x_1859_: *mut crate::leanh::LeanObject,
    mut v_x_1860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1867_: u8 = 0;
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1873_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1861_ = crate::leanh::lean_ctor_get(v_x_1859_, 0);
                crate::leanh::lean_inc(v_fst_1861_);
                v_snd_1862_ = crate::leanh::lean_ctor_get(v_x_1859_, 1);
                crate::leanh::lean_inc(v_snd_1862_);
                crate::leanh::lean_dec_ref(v_x_1859_);
                v_fst_1863_ = crate::leanh::lean_ctor_get(v_x_1860_, 0);
                v_snd_1864_ = crate::leanh::lean_ctor_get(v_x_1860_, 1);
                v_isSharedCheck_1873_ = (!crate::leanh::lean_is_exclusive(v_x_1860_)) as u8;
                if v_isSharedCheck_1873_ == 0 {
                    v___x_1866_ = v_x_1860_;
                    v_isShared_1867_ = v_isSharedCheck_1873_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1864_);
                    crate::leanh::lean_inc(v_fst_1863_);
                    crate::leanh::lean_dec(v_x_1860_);
                    v___x_1866_ = crate::leanh::lean_box(0);
                    v_isShared_1867_ = v_isSharedCheck_1873_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1868_ = lean_array_push(v_fst_1861_, v_fst_1863_);
                v___x_1869_ = lean_array_push(v_snd_1862_, v_snd_1864_);
                if v_isShared_1867_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1866_, 1, v___x_1869_);
                    crate::leanh::lean_ctor_set(v___x_1866_, 0, v___x_1868_);
                    v___x_1871_ = v___x_1866_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1872_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1868_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1872_, 1, v___x_1869_);
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
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(
    mut v_x_1874_: *mut crate::leanh::LeanObject,
    mut v_s_1875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_1876_ = crate::leanh::lean_ctor_get(v_s_1875_, 0);
    crate::leanh::lean_inc_n(v_fst_1876_, 3);
    v___x_1877_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1877_, 0, v_fst_1876_);
    crate::leanh::lean_ctor_set(v___x_1877_, 1, v_fst_1876_);
    crate::leanh::lean_ctor_set(v___x_1877_, 2, v_fst_1876_);
    return v___x_1877_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed(
    mut v_x_1878_: *mut crate::leanh::LeanObject,
    mut v_s_1879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1880_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(v_x_1878_, v_s_1879_);
    crate::leanh::lean_dec_ref(v_s_1879_);
    crate::leanh::lean_dec_ref(v_x_1878_);
    return v_res_1880_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__2_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(
    mut v_x_1881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1882_ = crate::leanh::lean_box(0);
    return v___x_1882_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__2_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed(
    mut v_x_1883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1884_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__2_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(v_x_1883_);
    crate::leanh::lean_dec_ref(v_x_1883_);
    return v_res_1884_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__3_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(
    mut v_x_1885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_1886_ = crate::leanh::lean_ctor_get(v_x_1885_, 0);
    crate::leanh::lean_inc(v_fst_1886_);
    return v_fst_1886_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__3_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed(
    mut v_x_1887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1888_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__3_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(v_x_1887_);
    crate::leanh::lean_dec_ref(v_x_1887_);
    return v_res_1888_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__spec__0(
    mut v_as_1889_: *mut crate::leanh::LeanObject,
    mut v_i_1890_: usize,
    mut v_stop_1891_: usize,
    mut v_b_1892_: *mut crate::leanh::LeanObject,
    mut v___y_1893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1895_: u8 = 0;
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: usize = 0;
    let mut v___x_1901_: usize = 0;
    let mut v_a_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1906_: u8 = 0;
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1910_: u8 = 0;
    let mut v___x_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1895_ = lean_usize_dec_eq(v_i_1890_, v_stop_1891_);
                if v___x_1895_ == 0 {
                    v___x_1896_ = lean_array_uget_borrowed(v_as_1889_, v_i_1890_);
                    crate::leanh::lean_inc(v___x_1896_);
                    v___x_1897_ = l_Lean_CodeAction_mkHoleCodeAction(v___x_1896_, v___y_1893_);
                    if crate::leanh::lean_obj_tag(v___x_1897_) == 0 {
                        v_a_1898_ = crate::leanh::lean_ctor_get(v___x_1897_, 0);
                        crate::leanh::lean_inc(v_a_1898_);
                        crate::leanh::lean_dec_ref_known(v___x_1897_, 1);
                        v___x_1899_ = lean_array_push(v_b_1892_, v_a_1898_);
                        v___x_1900_ = 1usize;
                        v___x_1901_ = lean_usize_add(v_i_1890_, v___x_1900_);
                        v_i_1890_ = v___x_1901_;
                        v_b_1892_ = v___x_1899_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_b_1892_);
                        v_a_1903_ = crate::leanh::lean_ctor_get(v___x_1897_, 0);
                        v_isSharedCheck_1910_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1897_)) as u8;
                        if v_isSharedCheck_1910_ == 0 {
                            v___x_1905_ = v___x_1897_;
                            v_isShared_1906_ = v_isSharedCheck_1910_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1903_);
                            crate::leanh::lean_dec(v___x_1897_);
                            v___x_1905_ = crate::leanh::lean_box(0);
                            v_isShared_1906_ = v_isSharedCheck_1910_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_1911_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1911_, 0, v_b_1892_);
                    return v___x_1911_;
                }
            }
            1 => {
                if v_isShared_1906_ == 0 {
                    v___x_1908_ = v___x_1905_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1909_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
                    v___x_1908_ = v_reuseFailAlloc_1909_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1908_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__spec__0___boxed(
    mut v_as_1912_: *mut crate::leanh::LeanObject,
    mut v_i_1913_: *mut crate::leanh::LeanObject,
    mut v_stop_1914_: *mut crate::leanh::LeanObject,
    mut v_b_1915_: *mut crate::leanh::LeanObject,
    mut v___y_1916_: *mut crate::leanh::LeanObject,
    mut v___y_1917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1918_: usize = 0;
    let mut v_stop_boxed_1919_: usize = 0;
    let mut v_res_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1918_ = crate::leanh::lean_unbox_usize(v_i_1913_);
    crate::leanh::lean_dec(v_i_1913_);
    v_stop_boxed_1919_ = crate::leanh::lean_unbox_usize(v_stop_1914_);
    crate::leanh::lean_dec(v_stop_1914_);
    v_res_1920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__spec__0(v_as_1912_, v_i_boxed_1918_, v_stop_boxed_1919_, v_b_1915_, v___y_1916_);
    crate::leanh::lean_dec_ref(v___y_1916_);
    crate::leanh::lean_dec_ref(v_as_1912_);
    return v_res_1920_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__spec__1(
    mut v_as_1921_: *mut crate::leanh::LeanObject,
    mut v_i_1922_: usize,
    mut v_stop_1923_: usize,
    mut v_b_1924_: *mut crate::leanh::LeanObject,
    mut v___y_1925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: usize = 0;
    let mut v___x_1930_: usize = 0;
    let mut v___y_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: u8 = 0;
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: u8 = 0;
    let mut v___x_1940_: u8 = 0;
    let mut v___x_1941_: usize = 0;
    let mut v___x_1942_: usize = 0;
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: usize = 0;
    let mut v___x_1945_: usize = 0;
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1935_ = lean_usize_dec_eq(v_i_1922_, v_stop_1923_);
                if v___x_1935_ == 0 {
                    v___x_1936_ = lean_array_uget_borrowed(v_as_1921_, v_i_1922_);
                    v___x_1937_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1938_ = lean_array_get_size(v___x_1936_);
                    v___x_1939_ = lean_nat_dec_lt(v___x_1937_, v___x_1938_);
                    if v___x_1939_ == 0 {
                        v_a_1928_ = v_b_1924_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1940_ = lean_nat_dec_le(v___x_1938_, v___x_1938_);
                        if v___x_1940_ == 0 {
                            if v___x_1939_ == 0 {
                                v_a_1928_ = v_b_1924_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1941_ = 0usize;
                                v___x_1942_ = lean_usize_of_nat(v___x_1938_);
                                v___x_1943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__spec__0(v___x_1936_, v___x_1941_, v___x_1942_, v_b_1924_, v___y_1925_);
                                v___y_1933_ = v___x_1943_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_1944_ = 0usize;
                            v___x_1945_ = lean_usize_of_nat(v___x_1938_);
                            v___x_1946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__spec__0(v___x_1936_, v___x_1944_, v___x_1945_, v_b_1924_, v___y_1925_);
                            v___y_1933_ = v___x_1946_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_1947_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1947_, 0, v_b_1924_);
                    return v___x_1947_;
                }
            }
            1 => {
                v___x_1929_ = 1usize;
                v___x_1930_ = lean_usize_add(v_i_1922_, v___x_1929_);
                v_i_1922_ = v___x_1930_;
                v_b_1924_ = v_a_1928_;
                state = 0;
                continue;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_1933_) == 0 {
                    v_a_1934_ = crate::leanh::lean_ctor_get(v___y_1933_, 0);
                    crate::leanh::lean_inc(v_a_1934_);
                    crate::leanh::lean_dec_ref_known(v___y_1933_, 1);
                    v_a_1928_ = v_a_1934_;
                    state = 1;
                    continue;
                } else {
                    return v___y_1933_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__spec__1___boxed(
    mut v_as_1948_: *mut crate::leanh::LeanObject,
    mut v_i_1949_: *mut crate::leanh::LeanObject,
    mut v_stop_1950_: *mut crate::leanh::LeanObject,
    mut v_b_1951_: *mut crate::leanh::LeanObject,
    mut v___y_1952_: *mut crate::leanh::LeanObject,
    mut v___y_1953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1954_: usize = 0;
    let mut v_stop_boxed_1955_: usize = 0;
    let mut v_res_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1954_ = crate::leanh::lean_unbox_usize(v_i_1949_);
    crate::leanh::lean_dec(v_i_1949_);
    v_stop_boxed_1955_ = crate::leanh::lean_unbox_usize(v_stop_1950_);
    crate::leanh::lean_dec(v_stop_1950_);
    v_res_1956_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__spec__1(v_as_1948_, v_i_boxed_1954_, v_stop_boxed_1955_, v_b_1951_, v___y_1952_);
    crate::leanh::lean_dec_ref(v___y_1952_);
    crate::leanh::lean_dec_ref(v_as_1948_);
    return v_res_1956_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__4_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(
    mut v___x_1957_: *mut crate::leanh::LeanObject,
    mut v___x_1958_: *mut crate::leanh::LeanObject,
    mut v___x_1959_: *mut crate::leanh::LeanObject,
    mut v_as_1960_: *mut crate::leanh::LeanObject,
    mut v___y_1961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1973_: u8 = 0;
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1977_: u8 = 0;
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: u8 = 0;
    let mut v___x_1980_: u8 = 0;
    let mut v___x_1981_: usize = 0;
    let mut v___x_1982_: usize = 0;
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: usize = 0;
    let mut v___x_1985_: usize = 0;
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1978_ = lean_array_get_size(v_as_1960_);
                v___x_1979_ = lean_nat_dec_lt(v___x_1958_, v___x_1978_);
                if v___x_1979_ == 0 {
                    v_a_1964_ = v___x_1959_;
                    state = 1;
                    continue;
                } else {
                    v___x_1980_ = lean_nat_dec_le(v___x_1978_, v___x_1978_);
                    if v___x_1980_ == 0 {
                        if v___x_1979_ == 0 {
                            v_a_1964_ = v___x_1959_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1981_ = 0usize;
                            v___x_1982_ = lean_usize_of_nat(v___x_1978_);
                            v___x_1983_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__spec__1(v_as_1960_, v___x_1981_, v___x_1982_, v___x_1959_, v___y_1961_);
                            v___y_1968_ = v___x_1983_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_1984_ = 0usize;
                        v___x_1985_ = lean_usize_of_nat(v___x_1978_);
                        v___x_1986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__spec__1(v_as_1960_, v___x_1984_, v___x_1985_, v___x_1959_, v___y_1961_);
                        v___y_1968_ = v___x_1986_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1965_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1965_, 0, v___x_1957_);
                crate::leanh::lean_ctor_set(v___x_1965_, 1, v_a_1964_);
                v___x_1966_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1966_, 0, v___x_1965_);
                return v___x_1966_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_1968_) == 0 {
                    v_a_1969_ = crate::leanh::lean_ctor_get(v___y_1968_, 0);
                    crate::leanh::lean_inc(v_a_1969_);
                    crate::leanh::lean_dec_ref_known(v___y_1968_, 1);
                    v_a_1964_ = v_a_1969_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___x_1957_);
                    v_a_1970_ = crate::leanh::lean_ctor_get(v___y_1968_, 0);
                    v_isSharedCheck_1977_ = (!crate::leanh::lean_is_exclusive(v___y_1968_)) as u8;
                    if v_isSharedCheck_1977_ == 0 {
                        v___x_1972_ = v___y_1968_;
                        v_isShared_1973_ = v_isSharedCheck_1977_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1970_);
                        crate::leanh::lean_dec(v___y_1968_);
                        v___x_1972_ = crate::leanh::lean_box(0);
                        v_isShared_1973_ = v_isSharedCheck_1977_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1973_ == 0 {
                    v___x_1975_ = v___x_1972_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1976_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1970_);
                    v___x_1975_ = v_reuseFailAlloc_1976_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1975_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__4_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed(
    mut v___x_1987_: *mut crate::leanh::LeanObject,
    mut v___x_1988_: *mut crate::leanh::LeanObject,
    mut v___x_1989_: *mut crate::leanh::LeanObject,
    mut v_as_1990_: *mut crate::leanh::LeanObject,
    mut v___y_1991_: *mut crate::leanh::LeanObject,
    mut v___y_1992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1993_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__4_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(v___x_1987_, v___x_1988_, v___x_1989_, v_as_1990_, v___y_1991_);
    crate::leanh::lean_dec_ref(v___y_1991_);
    crate::leanh::lean_dec_ref(v_as_1990_);
    crate::leanh::lean_dec(v___x_1988_);
    return v_res_1993_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(
    mut v___x_1994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1996_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1996_, 0, v___x_1994_);
    return v___x_1996_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed(
    mut v___x_1997_: *mut crate::leanh::LeanObject,
    mut v___y_1998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1999_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(v___x_1997_);
    return v_res_1999_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2031_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__11_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_;
    v___x_2032_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2031_);
    return v___x_2032_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed(
    mut v_a_2033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2034_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_();
    return v_res_2034_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2035_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2035_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2036_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__0);
    v___x_2037_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2037_, 0, v___x_2036_);
    return v___x_2037_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2038_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1);
    v___x_2039_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2040_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2040_, 0, v___x_2039_);
    crate::leanh::lean_ctor_set(v___x_2040_, 1, v___x_2039_);
    crate::leanh::lean_ctor_set(v___x_2040_, 2, v___x_2039_);
    crate::leanh::lean_ctor_set(v___x_2040_, 3, v___x_2039_);
    crate::leanh::lean_ctor_set(v___x_2040_, 4, v___x_2038_);
    crate::leanh::lean_ctor_set(v___x_2040_, 5, v___x_2038_);
    crate::leanh::lean_ctor_set(v___x_2040_, 6, v___x_2038_);
    crate::leanh::lean_ctor_set(v___x_2040_, 7, v___x_2038_);
    crate::leanh::lean_ctor_set(v___x_2040_, 8, v___x_2038_);
    crate::leanh::lean_ctor_set(v___x_2040_, 9, v___x_2038_);
    return v___x_2040_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2041_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2042_ = lean_mk_empty_array_with_capacity(v___x_2041_);
    v___x_2043_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2043_, 0, v___x_2042_);
    return v___x_2043_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2044_: usize = 0;
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2044_ = 5usize;
    v___x_2045_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2046_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2047_ = lean_mk_empty_array_with_capacity(v___x_2046_);
    v___x_2048_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__3);
    v___x_2049_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_2049_, 0, v___x_2048_);
    crate::leanh::lean_ctor_set(v___x_2049_, 1, v___x_2047_);
    crate::leanh::lean_ctor_set(v___x_2049_, 2, v___x_2045_);
    crate::leanh::lean_ctor_set(v___x_2049_, 3, v___x_2045_);
    crate::leanh::lean_ctor_set_usize(v___x_2049_, 4, v___x_2044_);
    return v___x_2049_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2050_ = crate::leanh::lean_box(1);
    v___x_2051_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__4);
    v___x_2052_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1);
    v___x_2053_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2053_, 0, v___x_2052_);
    crate::leanh::lean_ctor_set(v___x_2053_, 1, v___x_2051_);
    crate::leanh::lean_ctor_set(v___x_2053_, 2, v___x_2050_);
    return v___x_2053_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0(
    mut v_msgData_2054_: *mut crate::leanh::LeanObject,
    mut v___y_2055_: *mut crate::leanh::LeanObject,
    mut v___y_2056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2058_ = lean_st_ref_get(v___y_2056_);
    v_env_2059_ = crate::leanh::lean_ctor_get(v___x_2058_, 0);
    crate::leanh::lean_inc_ref(v_env_2059_);
    crate::leanh::lean_dec(v___x_2058_);
    v_options_2060_ = crate::leanh::lean_ctor_get(v___y_2055_, 2);
    v___x_2061_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__2);
    v___x_2062_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__5);
    crate::leanh::lean_inc_ref(v_options_2060_);
    v___x_2063_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2063_, 0, v_env_2059_);
    crate::leanh::lean_ctor_set(v___x_2063_, 1, v___x_2061_);
    crate::leanh::lean_ctor_set(v___x_2063_, 2, v___x_2062_);
    crate::leanh::lean_ctor_set(v___x_2063_, 3, v_options_2060_);
    v___x_2064_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2064_, 0, v___x_2063_);
    crate::leanh::lean_ctor_set(v___x_2064_, 1, v_msgData_2054_);
    v___x_2065_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2065_, 0, v___x_2064_);
    return v___x_2065_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_msgData_2066_: *mut crate::leanh::LeanObject,
    mut v___y_2067_: *mut crate::leanh::LeanObject,
    mut v___y_2068_: *mut crate::leanh::LeanObject,
    mut v___y_2069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2070_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0(v_msgData_2066_, v___y_2067_, v___y_2068_);
    crate::leanh::lean_dec(v___y_2068_);
    crate::leanh::lean_dec_ref(v___y_2067_);
    return v_res_2070_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0___redArg(
    mut v_msg_2071_: *mut crate::leanh::LeanObject,
    mut v___y_2072_: *mut crate::leanh::LeanObject,
    mut v___y_2073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2080_: u8 = 0;
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2085_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2075_ = crate::leanh::lean_ctor_get(v___y_2072_, 5);
                v___x_2076_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0(v_msg_2071_, v___y_2072_, v___y_2073_);
                v_a_2077_ = crate::leanh::lean_ctor_get(v___x_2076_, 0);
                v_isSharedCheck_2085_ = (!crate::leanh::lean_is_exclusive(v___x_2076_)) as u8;
                if v_isSharedCheck_2085_ == 0 {
                    v___x_2079_ = v___x_2076_;
                    v_isShared_2080_ = v_isSharedCheck_2085_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2077_);
                    crate::leanh::lean_dec(v___x_2076_);
                    v___x_2079_ = crate::leanh::lean_box(0);
                    v_isShared_2080_ = v_isSharedCheck_2085_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_2075_);
                v___x_2081_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2081_, 0, v_ref_2075_);
                crate::leanh::lean_ctor_set(v___x_2081_, 1, v_a_2077_);
                if v_isShared_2080_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2079_, 1);
                    crate::leanh::lean_ctor_set(v___x_2079_, 0, v___x_2081_);
                    v___x_2083_ = v___x_2079_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2084_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2081_);
                    v___x_2083_ = v_reuseFailAlloc_2084_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2083_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_msg_2086_: *mut crate::leanh::LeanObject,
    mut v___y_2087_: *mut crate::leanh::LeanObject,
    mut v___y_2088_: *mut crate::leanh::LeanObject,
    mut v___y_2089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2090_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0___redArg(v_msg_2086_, v___y_2087_, v___y_2088_);
    crate::leanh::lean_dec(v___y_2088_);
    crate::leanh::lean_dec_ref(v___y_2087_);
    return v_res_2090_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2092_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__0;
    v___x_2093_ = l_Lean_stringToMessageData(v___x_2092_);
    return v___x_2093_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2095_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__2;
    v___x_2096_ = l_Lean_stringToMessageData(v___x_2095_);
    return v___x_2096_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2098_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__4;
    v___x_2099_ = l_Lean_stringToMessageData(v___x_2098_);
    return v___x_2099_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg(
    mut v_name_2103_: *mut crate::leanh::LeanObject,
    mut v_kind_2104_: u8,
    mut v___y_2105_: *mut crate::leanh::LeanObject,
    mut v___y_2106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2108_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__1_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__1);
                v___x_2109_ = l_Lean_MessageData_ofName(v_name_2103_);
                v___x_2110_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2110_, 0, v___x_2108_);
                crate::leanh::lean_ctor_set(v___x_2110_, 1, v___x_2109_);
                v___x_2111_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__3_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__3);
                v___x_2112_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2112_, 0, v___x_2110_);
                crate::leanh::lean_ctor_set(v___x_2112_, 1, v___x_2111_);
                match v_kind_2104_ {
                    0 => {
                        v___x_2121_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__6;
                        v___y_2114_ = v___x_2121_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v___x_2122_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__7;
                        v___y_2114_ = v___x_2122_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_2123_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__8;
                        v___y_2114_ = v___x_2123_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_2114_);
                v___x_2115_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2115_, 0, v___y_2114_);
                v___x_2116_ = l_Lean_MessageData_ofFormat(v___x_2115_);
                v___x_2117_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2117_, 0, v___x_2112_);
                crate::leanh::lean_ctor_set(v___x_2117_, 1, v___x_2116_);
                v___x_2118_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__5_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__5);
                v___x_2119_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2119_, 0, v___x_2117_);
                crate::leanh::lean_ctor_set(v___x_2119_, 1, v___x_2118_);
                v___x_2120_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0___redArg(v___x_2119_, v___y_2105_, v___y_2106_);
                return v___x_2120_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___boxed(
    mut v_name_2124_: *mut crate::leanh::LeanObject,
    mut v_kind_2125_: *mut crate::leanh::LeanObject,
    mut v___y_2126_: *mut crate::leanh::LeanObject,
    mut v___y_2127_: *mut crate::leanh::LeanObject,
    mut v___y_2128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_2129_: u8 = 0;
    let mut v_res_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_2129_ = (crate::leanh::lean_unbox(v_kind_2125_) as u8);
    v_res_2130_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg(v_name_2124_, v_kind_boxed_2129_, v___y_2126_, v___y_2127_);
    crate::leanh::lean_dec(v___y_2127_);
    crate::leanh::lean_dec_ref(v___y_2126_);
    return v_res_2130_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2131_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2131_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2132_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_);
    v___x_2133_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2133_, 0, v___x_2132_);
    return v___x_2133_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2134_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_);
    v___x_2135_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2135_, 0, v___x_2134_);
    crate::leanh::lean_ctor_set(v___x_2135_, 1, v___x_2134_);
    return v___x_2135_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_(
    mut v___x_2136_: *mut crate::leanh::LeanObject,
    mut v___x_2137_: *mut crate::leanh::LeanObject,
    mut v_decl_2138_: *mut crate::leanh::LeanObject,
    mut v_stx_2139_: *mut crate::leanh::LeanObject,
    mut v_kind_2140_: u8,
    mut v___y_2141_: *mut crate::leanh::LeanObject,
    mut v___y_2142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2150_: u8 = 0;
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2163_: u8 = 0;
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2175_: u8 = 0;
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2190_: u8 = 0;
    let mut v_unused_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2192_: u8 = 0;
    let mut v_a_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2196_: u8 = 0;
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2204_: u8 = 0;
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2209_: u8 = 0;
    let mut v_unused_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: u8 = 0;
    let mut v___x_2213_: u8 = 0;
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2211_ =
                    l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2139_, v___y_2141_, v___y_2142_);
                if crate::leanh::lean_obj_tag(v___x_2211_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2211_, 1);
                    v___x_2212_ = 0;
                    v___x_2213_ = l_Lean_instBEqAttributeKind_beq(v_kind_2140_, v___x_2212_);
                    if v___x_2213_ == 0 {
                        crate::leanh::lean_dec(v_decl_2138_);
                        crate::leanh::lean_dec(v___x_2137_);
                        v___x_2214_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg(v___x_2136_, v_kind_2140_, v___y_2141_, v___y_2142_);
                        return v___x_2214_;
                    } else {
                        v___y_2145_ = v___y_2141_;
                        v___y_2146_ = v___y_2142_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_decl_2138_);
                    crate::leanh::lean_dec(v___x_2137_);
                    crate::leanh::lean_dec(v___x_2136_);
                    return v___x_2211_;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_decl_2138_);
                v___x_2147_ = l_Lean_ensureAttrDeclIsMeta(
                    v___x_2136_,
                    v_decl_2138_,
                    v_kind_2140_,
                    v___y_2145_,
                    v___y_2146_,
                );
                if crate::leanh::lean_obj_tag(v___x_2147_) == 0 {
                    v_isSharedCheck_2209_ = (!crate::leanh::lean_is_exclusive(v___x_2147_)) as u8;
                    if v_isSharedCheck_2209_ == 0 {
                        v_unused_2210_ = crate::leanh::lean_ctor_get(v___x_2147_, 0);
                        crate::leanh::lean_dec(v_unused_2210_);
                        v___x_2149_ = v___x_2147_;
                        v_isShared_2150_ = v_isSharedCheck_2209_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2147_);
                        v___x_2149_ = crate::leanh::lean_box(0);
                        v_isShared_2150_ = v_isSharedCheck_2209_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_decl_2138_);
                    crate::leanh::lean_dec(v___x_2137_);
                    return v___x_2147_;
                }
            }
            2 => {
                v___x_2151_ = lean_st_ref_get(v___y_2146_);
                v_env_2152_ = crate::leanh::lean_ctor_get(v___x_2151_, 0);
                crate::leanh::lean_inc_ref(v_env_2152_);
                crate::leanh::lean_dec(v___x_2151_);
                crate::leanh::lean_inc(v_decl_2138_);
                v___x_2153_ = lean_decl_get_sorry_dep(v_env_2152_, v_decl_2138_);
                if crate::leanh::lean_obj_tag(v___x_2153_) == 0 {
                    crate::leanh::lean_del_object(v___x_2149_);
                    v___x_2154_ = lean_st_ref_get(v___y_2146_);
                    v_env_2155_ = crate::leanh::lean_ctor_get(v___x_2154_, 0);
                    crate::leanh::lean_inc_ref(v_env_2155_);
                    crate::leanh::lean_dec(v___x_2154_);
                    v_options_2156_ = crate::leanh::lean_ctor_get(v___y_2145_, 2);
                    v_ref_2157_ = crate::leanh::lean_ctor_get(v___y_2145_, 5);
                    crate::leanh::lean_inc_ref(v_options_2156_);
                    v___x_2158_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2158_, 0, v_env_2155_);
                    crate::leanh::lean_ctor_set(v___x_2158_, 1, v_options_2156_);
                    crate::leanh::lean_inc(v_decl_2138_);
                    v___x_2159_ = l_Lean_CodeAction_mkHoleCodeAction(v_decl_2138_, v___x_2158_);
                    crate::leanh::lean_dec_ref_known(v___x_2158_, 2);
                    if crate::leanh::lean_obj_tag(v___x_2159_) == 0 {
                        v_a_2160_ = crate::leanh::lean_ctor_get(v___x_2159_, 0);
                        v_isSharedCheck_2192_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2159_)) as u8;
                        if v_isSharedCheck_2192_ == 0 {
                            v___x_2162_ = v___x_2159_;
                            v_isShared_2163_ = v_isSharedCheck_2192_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2160_);
                            crate::leanh::lean_dec(v___x_2159_);
                            v___x_2162_ = crate::leanh::lean_box(0);
                            v_isShared_2163_ = v_isSharedCheck_2192_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_decl_2138_);
                        crate::leanh::lean_dec(v___x_2137_);
                        v_a_2193_ = crate::leanh::lean_ctor_get(v___x_2159_, 0);
                        v_isSharedCheck_2204_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2159_)) as u8;
                        if v_isSharedCheck_2204_ == 0 {
                            v___x_2195_ = v___x_2159_;
                            v_isShared_2196_ = v_isSharedCheck_2204_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2193_);
                            crate::leanh::lean_dec(v___x_2159_);
                            v___x_2195_ = crate::leanh::lean_box(0);
                            v_isShared_2196_ = v_isSharedCheck_2204_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_2153_, 1);
                    crate::leanh::lean_dec(v_decl_2138_);
                    crate::leanh::lean_dec(v___x_2137_);
                    v___x_2205_ = crate::leanh::lean_box(0);
                    if v_isShared_2150_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2149_, 0, v___x_2205_);
                        v___x_2207_ = v___x_2149_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2208_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2205_);
                        v___x_2207_ = v_reuseFailAlloc_2208_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2164_ = lean_st_ref_take(v___y_2146_);
                v_env_2165_ = crate::leanh::lean_ctor_get(v___x_2164_, 0);
                v_nextMacroScope_2166_ = crate::leanh::lean_ctor_get(v___x_2164_, 1);
                v_ngen_2167_ = crate::leanh::lean_ctor_get(v___x_2164_, 2);
                v_auxDeclNGen_2168_ = crate::leanh::lean_ctor_get(v___x_2164_, 3);
                v_traceState_2169_ = crate::leanh::lean_ctor_get(v___x_2164_, 4);
                v_messages_2170_ = crate::leanh::lean_ctor_get(v___x_2164_, 6);
                v_infoState_2171_ = crate::leanh::lean_ctor_get(v___x_2164_, 7);
                v_snapshotTasks_2172_ = crate::leanh::lean_ctor_get(v___x_2164_, 8);
                v_isSharedCheck_2190_ = (!crate::leanh::lean_is_exclusive(v___x_2164_)) as u8;
                if v_isSharedCheck_2190_ == 0 {
                    v_unused_2191_ = crate::leanh::lean_ctor_get(v___x_2164_, 5);
                    crate::leanh::lean_dec(v_unused_2191_);
                    v___x_2174_ = v___x_2164_;
                    v_isShared_2175_ = v_isSharedCheck_2190_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2172_);
                    crate::leanh::lean_inc(v_infoState_2171_);
                    crate::leanh::lean_inc(v_messages_2170_);
                    crate::leanh::lean_inc(v_traceState_2169_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2168_);
                    crate::leanh::lean_inc(v_ngen_2167_);
                    crate::leanh::lean_inc(v_nextMacroScope_2166_);
                    crate::leanh::lean_inc(v_env_2165_);
                    crate::leanh::lean_dec(v___x_2164_);
                    v___x_2174_ = crate::leanh::lean_box(0);
                    v_isShared_2175_ = v_isSharedCheck_2190_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2176_ = l_Lean_CodeAction_holeCodeActionExt;
                v_toEnvExtension_2177_ = crate::leanh::lean_ctor_get(v___x_2176_, 0);
                v_asyncMode_2178_ = crate::leanh::lean_ctor_get(v_toEnvExtension_2177_, 2);
                v___x_2179_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2179_, 0, v_decl_2138_);
                crate::leanh::lean_ctor_set(v___x_2179_, 1, v_a_2160_);
                v___x_2180_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_2176_,
                    v_env_2165_,
                    v___x_2179_,
                    v_asyncMode_2178_,
                    v___x_2137_,
                );
                v___x_2181_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_);
                if v_isShared_2175_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2174_, 5, v___x_2181_);
                    crate::leanh::lean_ctor_set(v___x_2174_, 0, v___x_2180_);
                    v___x_2183_ = v___x_2174_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2189_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2180_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2189_, 1, v_nextMacroScope_2166_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2189_, 2, v_ngen_2167_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2189_, 3, v_auxDeclNGen_2168_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2189_, 4, v_traceState_2169_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2189_, 5, v___x_2181_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2189_, 6, v_messages_2170_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2189_, 7, v_infoState_2171_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2189_, 8, v_snapshotTasks_2172_);
                    v___x_2183_ = v_reuseFailAlloc_2189_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2184_ = lean_st_ref_set(v___y_2146_, v___x_2183_);
                v___x_2185_ = crate::leanh::lean_box(0);
                if v_isShared_2163_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2162_, 0, v___x_2185_);
                    v___x_2187_ = v___x_2162_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2188_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2185_);
                    v___x_2187_ = v_reuseFailAlloc_2188_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2187_;
            }
            7 => {
                v___x_2197_ = lean_io_error_to_string(v_a_2193_);
                v___x_2198_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2198_, 0, v___x_2197_);
                v___x_2199_ = l_Lean_MessageData_ofFormat(v___x_2198_);
                crate::leanh::lean_inc(v_ref_2157_);
                v___x_2200_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2200_, 0, v_ref_2157_);
                crate::leanh::lean_ctor_set(v___x_2200_, 1, v___x_2199_);
                if v_isShared_2196_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2195_, 0, v___x_2200_);
                    v___x_2202_ = v___x_2195_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2203_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2200_);
                    v___x_2202_ = v_reuseFailAlloc_2203_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2202_;
            }
            9 => {
                return v___x_2207_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2____boxed(
    mut v___x_2215_: *mut crate::leanh::LeanObject,
    mut v___x_2216_: *mut crate::leanh::LeanObject,
    mut v_decl_2217_: *mut crate::leanh::LeanObject,
    mut v_stx_2218_: *mut crate::leanh::LeanObject,
    mut v_kind_2219_: *mut crate::leanh::LeanObject,
    mut v___y_2220_: *mut crate::leanh::LeanObject,
    mut v___y_2221_: *mut crate::leanh::LeanObject,
    mut v___y_2222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_2223_: u8 = 0;
    let mut v_res_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_2223_ = (crate::leanh::lean_unbox(v_kind_2219_) as u8);
    v_res_2224_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_(v___x_2215_, v___x_2216_, v_decl_2217_, v_stx_2218_, v_kind_boxed_2223_, v___y_2220_, v___y_2221_);
    crate::leanh::lean_dec(v___y_2221_);
    crate::leanh::lean_dec_ref(v___y_2220_);
    return v_res_2224_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2226_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_;
    v___x_2227_ = l_Lean_stringToMessageData(v___x_2226_);
    return v___x_2227_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2229_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_;
    v___x_2230_ = l_Lean_stringToMessageData(v___x_2229_);
    return v___x_2230_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_(
    mut v___x_2231_: *mut crate::leanh::LeanObject,
    mut v_decl_2232_: *mut crate::leanh::LeanObject,
    mut v___y_2233_: *mut crate::leanh::LeanObject,
    mut v___y_2234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2236_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_);
    v___x_2237_ = l_Lean_MessageData_ofName(v___x_2231_);
    v___x_2238_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2238_, 0, v___x_2236_);
    crate::leanh::lean_ctor_set(v___x_2238_, 1, v___x_2237_);
    v___x_2239_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_);
    v___x_2240_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2240_, 0, v___x_2238_);
    crate::leanh::lean_ctor_set(v___x_2240_, 1, v___x_2239_);
    v___x_2241_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0___redArg(v___x_2240_, v___y_2233_, v___y_2234_);
    return v___x_2241_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2____boxed(
    mut v___x_2242_: *mut crate::leanh::LeanObject,
    mut v_decl_2243_: *mut crate::leanh::LeanObject,
    mut v___y_2244_: *mut crate::leanh::LeanObject,
    mut v___y_2245_: *mut crate::leanh::LeanObject,
    mut v___y_2246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2247_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_(v___x_2242_, v_decl_2243_, v___y_2244_, v___y_2245_);
    crate::leanh::lean_dec(v___y_2245_);
    crate::leanh::lean_dec_ref(v___y_2244_);
    crate::leanh::lean_dec(v_decl_2243_);
    return v_res_2247_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2329_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__32_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_;
    v___x_2330_ = l_Lean_registerBuiltinAttribute(v___x_2329_);
    return v___x_2330_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2____boxed(
    mut v_a_2331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2332_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_();
    return v_res_2332_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0(
    mut v_00_u03b1_2333_: *mut crate::leanh::LeanObject,
    mut v_msg_2334_: *mut crate::leanh::LeanObject,
    mut v___y_2335_: *mut crate::leanh::LeanObject,
    mut v___y_2336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2338_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0___redArg(v_msg_2334_, v___y_2335_, v___y_2336_);
    return v___x_2338_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b1_2339_: *mut crate::leanh::LeanObject,
    mut v_msg_2340_: *mut crate::leanh::LeanObject,
    mut v___y_2341_: *mut crate::leanh::LeanObject,
    mut v___y_2342_: *mut crate::leanh::LeanObject,
    mut v___y_2343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2344_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0(v_00_u03b1_2339_, v_msg_2340_, v___y_2341_, v___y_2342_);
    crate::leanh::lean_dec(v___y_2342_);
    crate::leanh::lean_dec_ref(v___y_2341_);
    return v_res_2344_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1(
    mut v_00_u03b1_2345_: *mut crate::leanh::LeanObject,
    mut v_name_2346_: *mut crate::leanh::LeanObject,
    mut v_kind_2347_: u8,
    mut v___y_2348_: *mut crate::leanh::LeanObject,
    mut v___y_2349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2351_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg(v_name_2346_, v_kind_2347_, v___y_2348_, v___y_2349_);
    return v___x_2351_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___boxed(
    mut v_00_u03b1_2352_: *mut crate::leanh::LeanObject,
    mut v_name_2353_: *mut crate::leanh::LeanObject,
    mut v_kind_2354_: *mut crate::leanh::LeanObject,
    mut v___y_2355_: *mut crate::leanh::LeanObject,
    mut v___y_2356_: *mut crate::leanh::LeanObject,
    mut v___y_2357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_2358_: u8 = 0;
    let mut v_res_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_2358_ = (crate::leanh::lean_unbox(v_kind_2354_) as u8);
    v_res_2359_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1(v_00_u03b1_2352_, v_name_2353_, v_kind_boxed_2358_, v___y_2355_, v___y_2356_);
    crate::leanh::lean_dec(v___y_2356_);
    crate::leanh::lean_dec_ref(v___y_2355_);
    return v_res_2359_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1(
    mut v_n_2365_: *mut crate::leanh::LeanObject,
    mut v_env_2366_: *mut crate::leanh::LeanObject,
    mut v_opts_2367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2368_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__1;
    v___x_2369_ = l_Lean_Environment_evalConstCheck___redArg(
        v_env_2366_,
        v_opts_2367_,
        v___x_2368_,
        v_n_2365_,
    );
    return v___x_2369_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___boxed(
    mut v_n_2370_: *mut crate::leanh::LeanObject,
    mut v_env_2371_: *mut crate::leanh::LeanObject,
    mut v_opts_2372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2373_ =
        l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1(
            v_n_2370_,
            v_env_2371_,
            v_opts_2372_,
        );
    crate::leanh::lean_dec_ref(v_opts_2372_);
    return v_res_2373_;
}
pub unsafe fn l_Lean_CodeAction_mkCommandCodeAction(
    mut v_n_2374_: *mut crate::leanh::LeanObject,
    mut v_a_2375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_env_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_env_2377_ = crate::leanh::lean_ctor_get(v_a_2375_, 0);
    v_opts_2378_ = crate::leanh::lean_ctor_get(v_a_2375_, 1);
    crate::leanh::lean_inc_ref(v_env_2377_);
    v___x_2379_ =
        l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1(
            v_n_2374_,
            v_env_2377_,
            v_opts_2378_,
        );
    v___x_2380_ =
        l_IO_ofExcept___at___00Lean_CodeAction_mkHoleCodeAction_spec__0___redArg(v___x_2379_);
    return v___x_2380_;
}
pub unsafe fn l_Lean_CodeAction_mkCommandCodeAction___boxed(
    mut v_n_2381_: *mut crate::leanh::LeanObject,
    mut v_a_2382_: *mut crate::leanh::LeanObject,
    mut v_a_2383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2384_ = l_Lean_CodeAction_mkCommandCodeAction(v_n_2381_, v_a_2382_);
    crate::leanh::lean_dec_ref(v_a_2382_);
    return v_res_2384_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_CodeAction_CommandCodeActions_insert_spec__0___redArg(
    mut v_t_2399_: *mut crate::leanh::LeanObject,
    mut v_k_2400_: *mut crate::leanh::LeanObject,
    mut v_fallback_2401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_2399_) == 0 {
                    v_k_2402_ = crate::leanh::lean_ctor_get(v_t_2399_, 1);
                    v_v_2403_ = crate::leanh::lean_ctor_get(v_t_2399_, 2);
                    v_l_2404_ = crate::leanh::lean_ctor_get(v_t_2399_, 3);
                    v_r_2405_ = crate::leanh::lean_ctor_get(v_t_2399_, 4);
                    v___x_2406_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2400_, v_k_2402_);
                    match v___x_2406_ {
                        0 => {
                            v_t_2399_ = v_l_2404_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_inc(v_v_2403_);
                            return v_v_2403_;
                        }
                        _ => {
                            v_t_2399_ = v_r_2405_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_fallback_2401_);
                    return v_fallback_2401_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_CodeAction_CommandCodeActions_insert_spec__0___redArg___boxed(
    mut v_t_2409_: *mut crate::leanh::LeanObject,
    mut v_k_2410_: *mut crate::leanh::LeanObject,
    mut v_fallback_2411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2412_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_CodeAction_CommandCodeActions_insert_spec__0___redArg(v_t_2409_, v_k_2410_, v_fallback_2411_);
    crate::leanh::lean_dec(v_fallback_2411_);
    crate::leanh::lean_dec(v_k_2410_);
    crate::leanh::lean_dec(v_t_2409_);
    return v_res_2412_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_CommandCodeActions_insert_spec__1(
    mut v_action_2415_: *mut crate::leanh::LeanObject,
    mut v_as_2416_: *mut crate::leanh::LeanObject,
    mut v_i_2417_: usize,
    mut v_stop_2418_: usize,
    mut v_b_2419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2420_: u8 = 0;
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: usize = 0;
    let mut v___x_2427_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2420_ = lean_usize_dec_eq(v_i_2417_, v_stop_2418_);
                if v___x_2420_ == 0 {
                    v___x_2421_ = lean_array_uget_borrowed(v_as_2416_, v_i_2417_);
                    v___x_2422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_CommandCodeActions_insert_spec__1___closed__0;
                    v___x_2423_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_CodeAction_CommandCodeActions_insert_spec__0___redArg(v_b_2419_, v___x_2421_, v___x_2422_);
                    crate::leanh::lean_inc_ref(v_action_2415_);
                    v___x_2424_ = lean_array_push(v___x_2423_, v_action_2415_);
                    crate::leanh::lean_inc(v___x_2421_);
                    v___x_2425_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2421_, v___x_2424_, v_b_2419_);
                    v___x_2426_ = 1usize;
                    v___x_2427_ = lean_usize_add(v_i_2417_, v___x_2426_);
                    v_i_2417_ = v___x_2427_;
                    v_b_2419_ = v___x_2425_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_action_2415_);
                    return v_b_2419_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_CommandCodeActions_insert_spec__1___boxed(
    mut v_action_2429_: *mut crate::leanh::LeanObject,
    mut v_as_2430_: *mut crate::leanh::LeanObject,
    mut v_i_2431_: *mut crate::leanh::LeanObject,
    mut v_stop_2432_: *mut crate::leanh::LeanObject,
    mut v_b_2433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2434_: usize = 0;
    let mut v_stop_boxed_2435_: usize = 0;
    let mut v_res_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2434_ = crate::leanh::lean_unbox_usize(v_i_2431_);
    crate::leanh::lean_dec(v_i_2431_);
    v_stop_boxed_2435_ = crate::leanh::lean_unbox_usize(v_stop_2432_);
    crate::leanh::lean_dec(v_stop_2432_);
    v_res_2436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_CommandCodeActions_insert_spec__1(v_action_2429_, v_as_2430_, v_i_boxed_2434_, v_stop_boxed_2435_, v_b_2433_);
    crate::leanh::lean_dec_ref(v_as_2430_);
    return v_res_2436_;
}
pub unsafe fn l_Lean_CodeAction_CommandCodeActions_insert(
    mut v_self_2437_: *mut crate::leanh::LeanObject,
    mut v_tacticKinds_2438_: *mut crate::leanh::LeanObject,
    mut v_action_2439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: u8 = 0;
    let mut v_onAnyCmd_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_onCmd_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: u8 = 0;
    let mut v___x_2446_: u8 = 0;
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2449_: u8 = 0;
    let mut v___x_2450_: usize = 0;
    let mut v___x_2451_: usize = 0;
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2456_: u8 = 0;
    let mut v_unused_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2461_: u8 = 0;
    let mut v___x_2462_: usize = 0;
    let mut v___x_2463_: usize = 0;
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2468_: u8 = 0;
    let mut v_unused_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_onAnyCmd_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_onCmd_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2475_: u8 = 0;
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2480_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2440_ = lean_array_get_size(v_tacticKinds_2438_);
                v___x_2441_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2442_ = lean_nat_dec_eq(v___x_2440_, v___x_2441_);
                if v___x_2442_ == 0 {
                    v_onAnyCmd_2443_ = crate::leanh::lean_ctor_get(v_self_2437_, 0);
                    v_onCmd_2444_ = crate::leanh::lean_ctor_get(v_self_2437_, 1);
                    v___x_2445_ = lean_nat_dec_lt(v___x_2441_, v___x_2440_);
                    if v___x_2445_ == 0 {
                        crate::leanh::lean_dec_ref(v_action_2439_);
                        return v_self_2437_;
                    } else {
                        v___x_2446_ = lean_nat_dec_le(v___x_2440_, v___x_2440_);
                        if v___x_2446_ == 0 {
                            if v___x_2445_ == 0 {
                                crate::leanh::lean_dec_ref(v_action_2439_);
                                return v_self_2437_;
                            } else {
                                crate::leanh::lean_inc(v_onCmd_2444_);
                                crate::leanh::lean_inc_ref(v_onAnyCmd_2443_);
                                v_isSharedCheck_2456_ =
                                    (!crate::leanh::lean_is_exclusive(v_self_2437_)) as u8;
                                if v_isSharedCheck_2456_ == 0 {
                                    v_unused_2457_ = crate::leanh::lean_ctor_get(v_self_2437_, 1);
                                    crate::leanh::lean_dec(v_unused_2457_);
                                    v_unused_2458_ = crate::leanh::lean_ctor_get(v_self_2437_, 0);
                                    crate::leanh::lean_dec(v_unused_2458_);
                                    v___x_2448_ = v_self_2437_;
                                    v_isShared_2449_ = v_isSharedCheck_2456_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_self_2437_);
                                    v___x_2448_ = crate::leanh::lean_box(0);
                                    v_isShared_2449_ = v_isSharedCheck_2456_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_inc(v_onCmd_2444_);
                            crate::leanh::lean_inc_ref(v_onAnyCmd_2443_);
                            v_isSharedCheck_2468_ =
                                (!crate::leanh::lean_is_exclusive(v_self_2437_)) as u8;
                            if v_isSharedCheck_2468_ == 0 {
                                v_unused_2469_ = crate::leanh::lean_ctor_get(v_self_2437_, 1);
                                crate::leanh::lean_dec(v_unused_2469_);
                                v_unused_2470_ = crate::leanh::lean_ctor_get(v_self_2437_, 0);
                                crate::leanh::lean_dec(v_unused_2470_);
                                v___x_2460_ = v_self_2437_;
                                v_isShared_2461_ = v_isSharedCheck_2468_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_self_2437_);
                                v___x_2460_ = crate::leanh::lean_box(0);
                                v_isShared_2461_ = v_isSharedCheck_2468_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v_onAnyCmd_2471_ = crate::leanh::lean_ctor_get(v_self_2437_, 0);
                    v_onCmd_2472_ = crate::leanh::lean_ctor_get(v_self_2437_, 1);
                    v_isSharedCheck_2480_ = (!crate::leanh::lean_is_exclusive(v_self_2437_)) as u8;
                    if v_isSharedCheck_2480_ == 0 {
                        v___x_2474_ = v_self_2437_;
                        v_isShared_2475_ = v_isSharedCheck_2480_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_onCmd_2472_);
                        crate::leanh::lean_inc(v_onAnyCmd_2471_);
                        crate::leanh::lean_dec(v_self_2437_);
                        v___x_2474_ = crate::leanh::lean_box(0);
                        v_isShared_2475_ = v_isSharedCheck_2480_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2450_ = 0usize;
                v___x_2451_ = lean_usize_of_nat(v___x_2440_);
                v___x_2452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_CommandCodeActions_insert_spec__1(v_action_2439_, v_tacticKinds_2438_, v___x_2450_, v___x_2451_, v_onCmd_2444_);
                if v_isShared_2449_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2448_, 1, v___x_2452_);
                    v___x_2454_ = v___x_2448_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2455_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_onAnyCmd_2443_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2455_, 1, v___x_2452_);
                    v___x_2454_ = v_reuseFailAlloc_2455_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2454_;
            }
            3 => {
                v___x_2462_ = 0usize;
                v___x_2463_ = lean_usize_of_nat(v___x_2440_);
                v___x_2464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_CommandCodeActions_insert_spec__1(v_action_2439_, v_tacticKinds_2438_, v___x_2462_, v___x_2463_, v_onCmd_2444_);
                if v_isShared_2461_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2460_, 1, v___x_2464_);
                    v___x_2466_ = v___x_2460_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2467_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_onAnyCmd_2443_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2467_, 1, v___x_2464_);
                    v___x_2466_ = v_reuseFailAlloc_2467_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2466_;
            }
            5 => {
                v___x_2476_ = lean_array_push(v_onAnyCmd_2471_, v_action_2439_);
                if v_isShared_2475_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2474_, 0, v___x_2476_);
                    v___x_2478_ = v___x_2474_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2479_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2476_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2479_, 1, v_onCmd_2472_);
                    v___x_2478_ = v_reuseFailAlloc_2479_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2478_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_CodeAction_CommandCodeActions_insert___boxed(
    mut v_self_2481_: *mut crate::leanh::LeanObject,
    mut v_tacticKinds_2482_: *mut crate::leanh::LeanObject,
    mut v_action_2483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2484_ = l_Lean_CodeAction_CommandCodeActions_insert(
        v_self_2481_,
        v_tacticKinds_2482_,
        v_action_2483_,
    );
    crate::leanh::lean_dec_ref(v_tacticKinds_2482_);
    return v_res_2484_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_CodeAction_CommandCodeActions_insert_spec__0(
    mut v_00_u03b4_2485_: *mut crate::leanh::LeanObject,
    mut v_t_2486_: *mut crate::leanh::LeanObject,
    mut v_k_2487_: *mut crate::leanh::LeanObject,
    mut v_fallback_2488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2489_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_CodeAction_CommandCodeActions_insert_spec__0___redArg(v_t_2486_, v_k_2487_, v_fallback_2488_);
    return v___x_2489_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_CodeAction_CommandCodeActions_insert_spec__0___boxed(
    mut v_00_u03b4_2490_: *mut crate::leanh::LeanObject,
    mut v_t_2491_: *mut crate::leanh::LeanObject,
    mut v_k_2492_: *mut crate::leanh::LeanObject,
    mut v_fallback_2493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2494_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_CodeAction_CommandCodeActions_insert_spec__0(v_00_u03b4_2490_, v_t_2491_, v_k_2492_, v_fallback_2493_);
    crate::leanh::lean_dec(v_fallback_2493_);
    crate::leanh::lean_dec(v_k_2492_);
    crate::leanh::lean_dec(v_t_2491_);
    return v_res_2494_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_262607364____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2496_ = l_Lean_CodeAction_instInhabitedCommandCodeActions_default___closed__1;
    v___x_2497_ = lean_st_mk_ref(v___x_2496_);
    v___x_2498_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2498_, 0, v___x_2497_);
    return v___x_2498_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_262607364____hygCtx___hyg_2____boxed(
    mut v_a_2499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2500_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_262607364____hygCtx___hyg_2_();
    return v_res_2500_;
}
pub unsafe fn l_Lean_CodeAction_insertBuiltin(
    mut v_args_2501_: *mut crate::leanh::LeanObject,
    mut v_proc_2502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2504_ = l_Lean_CodeAction_builtinCmdCodeActions;
    v___x_2505_ = lean_st_ref_take(v___x_2504_);
    v___x_2506_ =
        l_Lean_CodeAction_CommandCodeActions_insert(v___x_2505_, v_args_2501_, v_proc_2502_);
    v___x_2507_ = lean_st_ref_set(v___x_2504_, v___x_2506_);
    v___x_2508_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2508_, 0, v___x_2507_);
    return v___x_2508_;
}
pub unsafe fn l_Lean_CodeAction_insertBuiltin___boxed(
    mut v_args_2509_: *mut crate::leanh::LeanObject,
    mut v_proc_2510_: *mut crate::leanh::LeanObject,
    mut v_a_2511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2512_ = l_Lean_CodeAction_insertBuiltin(v_args_2509_, v_proc_2510_);
    crate::leanh::lean_dec_ref(v_args_2509_);
    return v_res_2512_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(
    mut v_x_2513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_2514_ = crate::leanh::lean_ctor_get(v_x_2513_, 0);
    crate::leanh::lean_inc(v_fst_2514_);
    return v_fst_2514_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed(
    mut v_x_2515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2516_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(v_x_2515_);
    crate::leanh::lean_dec_ref(v_x_2515_);
    return v_res_2516_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(
    mut v_x_2517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2518_ = crate::leanh::lean_box(0);
    return v___x_2518_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed(
    mut v_x_2519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2520_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(v_x_2519_);
    crate::leanh::lean_dec_ref(v_x_2519_);
    return v_res_2520_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__2_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(
    mut v_x_2521_: *mut crate::leanh::LeanObject,
    mut v_s_2522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_2523_ = crate::leanh::lean_ctor_get(v_s_2522_, 0);
    crate::leanh::lean_inc_n(v_fst_2523_, 3);
    v___x_2524_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2524_, 0, v_fst_2523_);
    crate::leanh::lean_ctor_set(v___x_2524_, 1, v_fst_2523_);
    crate::leanh::lean_ctor_set(v___x_2524_, 2, v_fst_2523_);
    return v___x_2524_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__2_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed(
    mut v_x_2525_: *mut crate::leanh::LeanObject,
    mut v_s_2526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2527_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__2_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(v_x_2525_, v_s_2526_);
    crate::leanh::lean_dec_ref(v_s_2526_);
    crate::leanh::lean_dec_ref(v_x_2525_);
    return v_res_2527_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__3_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(
    mut v_x_2528_: *mut crate::leanh::LeanObject,
    mut v_x_2529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2536_: u8 = 0;
    let mut v_cmdKinds_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2543_: u8 = 0;
    let mut v_unused_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2530_ = crate::leanh::lean_ctor_get(v_x_2529_, 0);
                crate::leanh::lean_inc(v_fst_2530_);
                v_fst_2531_ = crate::leanh::lean_ctor_get(v_x_2528_, 0);
                crate::leanh::lean_inc(v_fst_2531_);
                v_snd_2532_ = crate::leanh::lean_ctor_get(v_x_2528_, 1);
                crate::leanh::lean_inc(v_snd_2532_);
                crate::leanh::lean_dec_ref(v_x_2528_);
                v_snd_2533_ = crate::leanh::lean_ctor_get(v_x_2529_, 1);
                v_isSharedCheck_2543_ = (!crate::leanh::lean_is_exclusive(v_x_2529_)) as u8;
                if v_isSharedCheck_2543_ == 0 {
                    v_unused_2544_ = crate::leanh::lean_ctor_get(v_x_2529_, 0);
                    crate::leanh::lean_dec(v_unused_2544_);
                    v___x_2535_ = v_x_2529_;
                    v_isShared_2536_ = v_isSharedCheck_2543_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2533_);
                    crate::leanh::lean_dec(v_x_2529_);
                    v___x_2535_ = crate::leanh::lean_box(0);
                    v_isShared_2536_ = v_isSharedCheck_2543_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_cmdKinds_2537_ = crate::leanh::lean_ctor_get(v_fst_2530_, 1);
                crate::leanh::lean_inc_ref(v_cmdKinds_2537_);
                v___x_2538_ = lean_array_push(v_fst_2531_, v_fst_2530_);
                v___x_2539_ = l_Lean_CodeAction_CommandCodeActions_insert(
                    v_snd_2532_,
                    v_cmdKinds_2537_,
                    v_snd_2533_,
                );
                crate::leanh::lean_dec_ref(v_cmdKinds_2537_);
                if v_isShared_2536_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2535_, 1, v___x_2539_);
                    crate::leanh::lean_ctor_set(v___x_2535_, 0, v___x_2538_);
                    v___x_2541_ = v___x_2535_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2542_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2542_, 0, v___x_2538_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2542_, 1, v___x_2539_);
                    v___x_2541_ = v_reuseFailAlloc_2542_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2541_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__4_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(
    mut v___x_2547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2549_ = lean_st_ref_get(v___x_2547_);
    v___x_2550_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__4___closed__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_;
    v___x_2551_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2551_, 0, v___x_2550_);
    crate::leanh::lean_ctor_set(v___x_2551_, 1, v___x_2549_);
    v___x_2552_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2552_, 0, v___x_2551_);
    return v___x_2552_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__4_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed(
    mut v___x_2553_: *mut crate::leanh::LeanObject,
    mut v___y_2554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2555_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__4_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(v___x_2553_);
    crate::leanh::lean_dec(v___x_2553_);
    return v_res_2555_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__spec__0(
    mut v_as_2556_: *mut crate::leanh::LeanObject,
    mut v_i_2557_: usize,
    mut v_stop_2558_: usize,
    mut v_b_2559_: *mut crate::leanh::LeanObject,
    mut v___y_2560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2562_: u8 = 0;
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdKinds_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: usize = 0;
    let mut v___x_2570_: usize = 0;
    let mut v_a_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2575_: u8 = 0;
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2579_: u8 = 0;
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2562_ = lean_usize_dec_eq(v_i_2557_, v_stop_2558_);
                if v___x_2562_ == 0 {
                    v___x_2563_ = lean_array_uget_borrowed(v_as_2556_, v_i_2557_);
                    v_declName_2564_ = crate::leanh::lean_ctor_get(v___x_2563_, 0);
                    v_cmdKinds_2565_ = crate::leanh::lean_ctor_get(v___x_2563_, 1);
                    crate::leanh::lean_inc(v_declName_2564_);
                    v___x_2566_ =
                        l_Lean_CodeAction_mkCommandCodeAction(v_declName_2564_, v___y_2560_);
                    if crate::leanh::lean_obj_tag(v___x_2566_) == 0 {
                        v_a_2567_ = crate::leanh::lean_ctor_get(v___x_2566_, 0);
                        crate::leanh::lean_inc(v_a_2567_);
                        crate::leanh::lean_dec_ref_known(v___x_2566_, 1);
                        v___x_2568_ = l_Lean_CodeAction_CommandCodeActions_insert(
                            v_b_2559_,
                            v_cmdKinds_2565_,
                            v_a_2567_,
                        );
                        v___x_2569_ = 1usize;
                        v___x_2570_ = lean_usize_add(v_i_2557_, v___x_2569_);
                        v_i_2557_ = v___x_2570_;
                        v_b_2559_ = v___x_2568_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_b_2559_);
                        v_a_2572_ = crate::leanh::lean_ctor_get(v___x_2566_, 0);
                        v_isSharedCheck_2579_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2566_)) as u8;
                        if v_isSharedCheck_2579_ == 0 {
                            v___x_2574_ = v___x_2566_;
                            v_isShared_2575_ = v_isSharedCheck_2579_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2572_);
                            crate::leanh::lean_dec(v___x_2566_);
                            v___x_2574_ = crate::leanh::lean_box(0);
                            v_isShared_2575_ = v_isSharedCheck_2579_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_2580_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2580_, 0, v_b_2559_);
                    return v___x_2580_;
                }
            }
            1 => {
                if v_isShared_2575_ == 0 {
                    v___x_2577_ = v___x_2574_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2578_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
                    v___x_2577_ = v_reuseFailAlloc_2578_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2577_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__spec__0___boxed(
    mut v_as_2581_: *mut crate::leanh::LeanObject,
    mut v_i_2582_: *mut crate::leanh::LeanObject,
    mut v_stop_2583_: *mut crate::leanh::LeanObject,
    mut v_b_2584_: *mut crate::leanh::LeanObject,
    mut v___y_2585_: *mut crate::leanh::LeanObject,
    mut v___y_2586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2587_: usize = 0;
    let mut v_stop_boxed_2588_: usize = 0;
    let mut v_res_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2587_ = crate::leanh::lean_unbox_usize(v_i_2582_);
    crate::leanh::lean_dec(v_i_2582_);
    v_stop_boxed_2588_ = crate::leanh::lean_unbox_usize(v_stop_2583_);
    crate::leanh::lean_dec(v_stop_2583_);
    v_res_2589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__spec__0(v_as_2581_, v_i_boxed_2587_, v_stop_boxed_2588_, v_b_2584_, v___y_2585_);
    crate::leanh::lean_dec_ref(v___y_2585_);
    crate::leanh::lean_dec_ref(v_as_2581_);
    return v_res_2589_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__spec__1(
    mut v_as_2590_: *mut crate::leanh::LeanObject,
    mut v_i_2591_: usize,
    mut v_stop_2592_: usize,
    mut v_b_2593_: *mut crate::leanh::LeanObject,
    mut v___y_2594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: usize = 0;
    let mut v___x_2599_: usize = 0;
    let mut v___y_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: u8 = 0;
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: u8 = 0;
    let mut v___x_2609_: u8 = 0;
    let mut v___x_2610_: usize = 0;
    let mut v___x_2611_: usize = 0;
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: usize = 0;
    let mut v___x_2614_: usize = 0;
    let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2604_ = lean_usize_dec_eq(v_i_2591_, v_stop_2592_);
                if v___x_2604_ == 0 {
                    v___x_2605_ = lean_array_uget_borrowed(v_as_2590_, v_i_2591_);
                    v___x_2606_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2607_ = lean_array_get_size(v___x_2605_);
                    v___x_2608_ = lean_nat_dec_lt(v___x_2606_, v___x_2607_);
                    if v___x_2608_ == 0 {
                        v_a_2597_ = v_b_2593_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2609_ = lean_nat_dec_le(v___x_2607_, v___x_2607_);
                        if v___x_2609_ == 0 {
                            if v___x_2608_ == 0 {
                                v_a_2597_ = v_b_2593_;
                                state = 1;
                                continue;
                            } else {
                                v___x_2610_ = 0usize;
                                v___x_2611_ = lean_usize_of_nat(v___x_2607_);
                                v___x_2612_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__spec__0(v___x_2605_, v___x_2610_, v___x_2611_, v_b_2593_, v___y_2594_);
                                v___y_2602_ = v___x_2612_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_2613_ = 0usize;
                            v___x_2614_ = lean_usize_of_nat(v___x_2607_);
                            v___x_2615_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__spec__0(v___x_2605_, v___x_2613_, v___x_2614_, v_b_2593_, v___y_2594_);
                            v___y_2602_ = v___x_2615_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_2616_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2616_, 0, v_b_2593_);
                    return v___x_2616_;
                }
            }
            1 => {
                v___x_2598_ = 1usize;
                v___x_2599_ = lean_usize_add(v_i_2591_, v___x_2598_);
                v_i_2591_ = v___x_2599_;
                v_b_2593_ = v_a_2597_;
                state = 0;
                continue;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_2602_) == 0 {
                    v_a_2603_ = crate::leanh::lean_ctor_get(v___y_2602_, 0);
                    crate::leanh::lean_inc(v_a_2603_);
                    crate::leanh::lean_dec_ref_known(v___y_2602_, 1);
                    v_a_2597_ = v_a_2603_;
                    state = 1;
                    continue;
                } else {
                    return v___y_2602_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__spec__1___boxed(
    mut v_as_2617_: *mut crate::leanh::LeanObject,
    mut v_i_2618_: *mut crate::leanh::LeanObject,
    mut v_stop_2619_: *mut crate::leanh::LeanObject,
    mut v_b_2620_: *mut crate::leanh::LeanObject,
    mut v___y_2621_: *mut crate::leanh::LeanObject,
    mut v___y_2622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2623_: usize = 0;
    let mut v_stop_boxed_2624_: usize = 0;
    let mut v_res_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2623_ = crate::leanh::lean_unbox_usize(v_i_2618_);
    crate::leanh::lean_dec(v_i_2618_);
    v_stop_boxed_2624_ = crate::leanh::lean_unbox_usize(v_stop_2619_);
    crate::leanh::lean_dec(v_stop_2619_);
    v_res_2625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__spec__1(v_as_2617_, v_i_boxed_2623_, v_stop_boxed_2624_, v_b_2620_, v___y_2621_);
    crate::leanh::lean_dec_ref(v___y_2621_);
    crate::leanh::lean_dec_ref(v_as_2617_);
    return v_res_2625_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(
    mut v___x_2626_: *mut crate::leanh::LeanObject,
    mut v_as_2627_: *mut crate::leanh::LeanObject,
    mut v___y_2628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2643_: u8 = 0;
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2647_: u8 = 0;
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: u8 = 0;
    let mut v___x_2650_: u8 = 0;
    let mut v___x_2651_: usize = 0;
    let mut v___x_2652_: usize = 0;
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: usize = 0;
    let mut v___x_2655_: usize = 0;
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2630_ = lean_st_ref_get(v___x_2626_);
                v___x_2631_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2648_ = lean_array_get_size(v_as_2627_);
                v___x_2649_ = lean_nat_dec_lt(v___x_2631_, v___x_2648_);
                if v___x_2649_ == 0 {
                    v_a_2633_ = v___x_2630_;
                    state = 1;
                    continue;
                } else {
                    v___x_2650_ = lean_nat_dec_le(v___x_2648_, v___x_2648_);
                    if v___x_2650_ == 0 {
                        if v___x_2649_ == 0 {
                            v_a_2633_ = v___x_2630_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2651_ = 0usize;
                            v___x_2652_ = lean_usize_of_nat(v___x_2648_);
                            v___x_2653_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__spec__1(v_as_2627_, v___x_2651_, v___x_2652_, v___x_2630_, v___y_2628_);
                            v___y_2638_ = v___x_2653_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_2654_ = 0usize;
                        v___x_2655_ = lean_usize_of_nat(v___x_2648_);
                        v___x_2656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__spec__1(v_as_2627_, v___x_2654_, v___x_2655_, v___x_2630_, v___y_2628_);
                        v___y_2638_ = v___x_2656_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2634_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__4___closed__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_;
                v___x_2635_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2635_, 0, v___x_2634_);
                crate::leanh::lean_ctor_set(v___x_2635_, 1, v_a_2633_);
                v___x_2636_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2636_, 0, v___x_2635_);
                return v___x_2636_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_2638_) == 0 {
                    v_a_2639_ = crate::leanh::lean_ctor_get(v___y_2638_, 0);
                    crate::leanh::lean_inc(v_a_2639_);
                    crate::leanh::lean_dec_ref_known(v___y_2638_, 1);
                    v_a_2633_ = v_a_2639_;
                    state = 1;
                    continue;
                } else {
                    v_a_2640_ = crate::leanh::lean_ctor_get(v___y_2638_, 0);
                    v_isSharedCheck_2647_ = (!crate::leanh::lean_is_exclusive(v___y_2638_)) as u8;
                    if v_isSharedCheck_2647_ == 0 {
                        v___x_2642_ = v___y_2638_;
                        v_isShared_2643_ = v_isSharedCheck_2647_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2640_);
                        crate::leanh::lean_dec(v___y_2638_);
                        v___x_2642_ = crate::leanh::lean_box(0);
                        v_isShared_2643_ = v_isSharedCheck_2647_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2643_ == 0 {
                    v___x_2645_ = v___x_2642_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2646_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2640_);
                    v___x_2645_ = v_reuseFailAlloc_2646_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2645_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed(
    mut v___x_2657_: *mut crate::leanh::LeanObject,
    mut v_as_2658_: *mut crate::leanh::LeanObject,
    mut v___y_2659_: *mut crate::leanh::LeanObject,
    mut v___y_2660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2661_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(v___x_2657_, v_as_2658_, v___y_2659_);
    crate::leanh::lean_dec_ref(v___y_2659_);
    crate::leanh::lean_dec_ref(v_as_2658_);
    crate::leanh::lean_dec(v___x_2657_);
    return v_res_2661_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2671_ = l_Lean_CodeAction_builtinCmdCodeActions;
    v___f_2672_ = crate::leanh::lean_alloc_closure(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__4_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___f_2672_, 0, v___x_2671_);
    return v___f_2672_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2673_ = l_Lean_CodeAction_builtinCmdCodeActions;
    v___f_2674_ = crate::leanh::lean_alloc_closure(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 4, 1);
    crate::leanh::lean_closure_set(v___f_2674_, 0, v___x_2673_);
    return v___f_2674_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2675_ = crate::leanh::lean_box(0);
    v___x_2676_ = crate::leanh::lean_box(2);
    v___f_2677_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_;
    v___f_2678_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_;
    v___f_2679_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_;
    v___f_2680_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_);
    v___f_2681_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_);
    v___x_2682_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_;
    v___x_2683_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2683_, 0, v___x_2682_);
    crate::leanh::lean_ctor_set(v___x_2683_, 1, v___f_2681_);
    crate::leanh::lean_ctor_set(v___x_2683_, 2, v___f_2680_);
    crate::leanh::lean_ctor_set(v___x_2683_, 3, v___f_2679_);
    crate::leanh::lean_ctor_set(v___x_2683_, 4, v___f_2678_);
    crate::leanh::lean_ctor_set(v___x_2683_, 5, v___f_2677_);
    crate::leanh::lean_ctor_set(v___x_2683_, 6, v___x_2676_);
    crate::leanh::lean_ctor_set(v___x_2683_, 7, v___x_2675_);
    return v___x_2683_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2684_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_;
    v___x_2685_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_);
    v___x_2686_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2686_, 0, v___x_2685_);
    crate::leanh::lean_ctor_set(v___x_2686_, 1, v___f_2684_);
    return v___x_2686_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2688_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_);
    v___x_2689_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2688_);
    return v___x_2689_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed(
    mut v_a_2690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2691_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_();
    return v_res_2691_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___closed__0()
-> f64 {
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: f64 = 0.0;
    v___x_2692_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2693_ = lean_float_of_nat(v___x_2692_);
    return v___x_2693_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3(
    mut v_cls_2697_: *mut crate::leanh::LeanObject,
    mut v_msg_2698_: *mut crate::leanh::LeanObject,
    mut v___y_2699_: *mut crate::leanh::LeanObject,
    mut v___y_2700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2707_: u8 = 0;
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2720_: u8 = 0;
    let mut v_tid_2721_: u64 = 0;
    let mut v_traces_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2725_: u8 = 0;
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: f64 = 0.0;
    let mut v___x_2728_: u8 = 0;
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2746_: u8 = 0;
    let mut v_isSharedCheck_2747_: u8 = 0;
    let mut v_isSharedCheck_2748_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2702_ = crate::leanh::lean_ctor_get(v___y_2699_, 5);
                v___x_2703_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0(v_msg_2698_, v___y_2699_, v___y_2700_);
                v_a_2704_ = crate::leanh::lean_ctor_get(v___x_2703_, 0);
                v_isSharedCheck_2748_ = (!crate::leanh::lean_is_exclusive(v___x_2703_)) as u8;
                if v_isSharedCheck_2748_ == 0 {
                    v___x_2706_ = v___x_2703_;
                    v_isShared_2707_ = v_isSharedCheck_2748_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2704_);
                    crate::leanh::lean_dec(v___x_2703_);
                    v___x_2706_ = crate::leanh::lean_box(0);
                    v_isShared_2707_ = v_isSharedCheck_2748_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2708_ = lean_st_ref_take(v___y_2700_);
                v_traceState_2709_ = crate::leanh::lean_ctor_get(v___x_2708_, 4);
                v_env_2710_ = crate::leanh::lean_ctor_get(v___x_2708_, 0);
                v_nextMacroScope_2711_ = crate::leanh::lean_ctor_get(v___x_2708_, 1);
                v_ngen_2712_ = crate::leanh::lean_ctor_get(v___x_2708_, 2);
                v_auxDeclNGen_2713_ = crate::leanh::lean_ctor_get(v___x_2708_, 3);
                v_cache_2714_ = crate::leanh::lean_ctor_get(v___x_2708_, 5);
                v_messages_2715_ = crate::leanh::lean_ctor_get(v___x_2708_, 6);
                v_infoState_2716_ = crate::leanh::lean_ctor_get(v___x_2708_, 7);
                v_snapshotTasks_2717_ = crate::leanh::lean_ctor_get(v___x_2708_, 8);
                v_isSharedCheck_2747_ = (!crate::leanh::lean_is_exclusive(v___x_2708_)) as u8;
                if v_isSharedCheck_2747_ == 0 {
                    v___x_2719_ = v___x_2708_;
                    v_isShared_2720_ = v_isSharedCheck_2747_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2717_);
                    crate::leanh::lean_inc(v_infoState_2716_);
                    crate::leanh::lean_inc(v_messages_2715_);
                    crate::leanh::lean_inc(v_cache_2714_);
                    crate::leanh::lean_inc(v_traceState_2709_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2713_);
                    crate::leanh::lean_inc(v_ngen_2712_);
                    crate::leanh::lean_inc(v_nextMacroScope_2711_);
                    crate::leanh::lean_inc(v_env_2710_);
                    crate::leanh::lean_dec(v___x_2708_);
                    v___x_2719_ = crate::leanh::lean_box(0);
                    v_isShared_2720_ = v_isSharedCheck_2747_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2721_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_2709_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_2722_ = crate::leanh::lean_ctor_get(v_traceState_2709_, 0);
                v_isSharedCheck_2746_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_2709_)) as u8;
                if v_isSharedCheck_2746_ == 0 {
                    v___x_2724_ = v_traceState_2709_;
                    v_isShared_2725_ = v_isSharedCheck_2746_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_2722_);
                    crate::leanh::lean_dec(v_traceState_2709_);
                    v___x_2724_ = crate::leanh::lean_box(0);
                    v_isShared_2725_ = v_isSharedCheck_2746_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2726_ = crate::leanh::lean_box(0);
                v___x_2727_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___closed__0);
                v___x_2728_ = 0;
                v___x_2729_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___closed__1;
                v___x_2730_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_2730_, 0, v_cls_2697_);
                crate::leanh::lean_ctor_set(v___x_2730_, 1, v___x_2726_);
                crate::leanh::lean_ctor_set(v___x_2730_, 2, v___x_2729_);
                crate::leanh::lean_ctor_set_float(
                    v___x_2730_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_2727_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_2730_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_2727_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2730_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_2728_,
                );
                v___x_2731_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___closed__2;
                v___x_2732_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2732_, 0, v___x_2730_);
                crate::leanh::lean_ctor_set(v___x_2732_, 1, v_a_2704_);
                crate::leanh::lean_ctor_set(v___x_2732_, 2, v___x_2731_);
                crate::leanh::lean_inc(v_ref_2702_);
                v___x_2733_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2733_, 0, v_ref_2702_);
                crate::leanh::lean_ctor_set(v___x_2733_, 1, v___x_2732_);
                v___x_2734_ = l_Lean_PersistentArray_push___redArg(v_traces_2722_, v___x_2733_);
                if v_isShared_2725_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2724_, 0, v___x_2734_);
                    v___x_2736_ = v___x_2724_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2745_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2745_, 0, v___x_2734_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2745_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_2721_,
                    );
                    v___x_2736_ = v_reuseFailAlloc_2745_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2720_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2719_, 4, v___x_2736_);
                    v___x_2738_ = v___x_2719_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2744_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_env_2710_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2744_, 1, v_nextMacroScope_2711_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2744_, 2, v_ngen_2712_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2744_, 3, v_auxDeclNGen_2713_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2744_, 4, v___x_2736_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2744_, 5, v_cache_2714_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2744_, 6, v_messages_2715_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2744_, 7, v_infoState_2716_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2744_, 8, v_snapshotTasks_2717_);
                    v___x_2738_ = v_reuseFailAlloc_2744_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2739_ = lean_st_ref_set(v___y_2700_, v___x_2738_);
                v___x_2740_ = crate::leanh::lean_box(0);
                if v_isShared_2707_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2706_, 0, v___x_2740_);
                    v___x_2742_ = v___x_2706_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2743_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___x_2740_);
                    v___x_2742_ = v_reuseFailAlloc_2743_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2742_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___boxed(
    mut v_cls_2749_: *mut crate::leanh::LeanObject,
    mut v_msg_2750_: *mut crate::leanh::LeanObject,
    mut v___y_2751_: *mut crate::leanh::LeanObject,
    mut v___y_2752_: *mut crate::leanh::LeanObject,
    mut v___y_2753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2754_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3(v_cls_2749_, v_msg_2750_, v___y_2751_, v___y_2752_);
    crate::leanh::lean_dec(v___y_2752_);
    crate::leanh::lean_dec_ref(v___y_2751_);
    return v_res_2754_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4_spec__7___redArg(
    mut v_keys_2755_: *mut crate::leanh::LeanObject,
    mut v_i_2756_: *mut crate::leanh::LeanObject,
    mut v_k_2757_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: u8 = 0;
    let mut v_k_x27_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: u8 = 0;
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2758_ = lean_array_get_size(v_keys_2755_);
                v___x_2759_ = lean_nat_dec_lt(v_i_2756_, v___x_2758_);
                if v___x_2759_ == 0 {
                    crate::leanh::lean_dec(v_i_2756_);
                    return v___x_2759_;
                } else {
                    v_k_x27_2760_ = lean_array_fget_borrowed(v_keys_2755_, v_i_2756_);
                    v___x_2761_ = l_Lean_instBEqExtraModUse_beq(v_k_2757_, v_k_x27_2760_);
                    if v___x_2761_ == 0 {
                        v___x_2762_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2763_ = lean_nat_add(v_i_2756_, v___x_2762_);
                        crate::leanh::lean_dec(v_i_2756_);
                        v_i_2756_ = v___x_2763_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_2756_);
                        return v___x_2761_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4_spec__7___redArg___boxed(
    mut v_keys_2765_: *mut crate::leanh::LeanObject,
    mut v_i_2766_: *mut crate::leanh::LeanObject,
    mut v_k_2767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2768_: u8 = 0;
    let mut v_r_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2768_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4_spec__7___redArg(v_keys_2765_, v_i_2766_, v_k_2767_);
    crate::leanh::lean_dec_ref(v_k_2767_);
    crate::leanh::lean_dec_ref(v_keys_2765_);
    v_r_2769_ = crate::leanh::lean_box((v_res_2768_) as usize);
    return v_r_2769_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__0()
-> usize {
    let mut v___x_2770_: usize = 0;
    let mut v___x_2771_: usize = 0;
    let mut v___x_2772_: usize = 0;
    v___x_2770_ = 5usize;
    v___x_2771_ = 1usize;
    v___x_2772_ = lean_usize_shift_left(v___x_2771_, v___x_2770_);
    return v___x_2772_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__1()
-> usize {
    let mut v___x_2773_: usize = 0;
    let mut v___x_2774_: usize = 0;
    let mut v___x_2775_: usize = 0;
    v___x_2773_ = 1usize;
    v___x_2774_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__0);
    v___x_2775_ = lean_usize_sub(v___x_2774_, v___x_2773_);
    return v___x_2775_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg(
    mut v_x_2776_: *mut crate::leanh::LeanObject,
    mut v_x_2777_: usize,
    mut v_x_2778_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: usize = 0;
    let mut v___x_2782_: usize = 0;
    let mut v___x_2783_: usize = 0;
    let mut v_j_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: u8 = 0;
    let mut v_node_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: usize = 0;
    let mut v___x_2791_: u8 = 0;
    let mut v_ks_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2776_) == 0 {
                    v_es_2779_ = crate::leanh::lean_ctor_get(v_x_2776_, 0);
                    v___x_2780_ = crate::leanh::lean_box(2);
                    v___x_2781_ = 5usize;
                    v___x_2782_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__1);
                    v___x_2783_ = lean_usize_land(v_x_2777_, v___x_2782_);
                    v_j_2784_ = lean_usize_to_nat(v___x_2783_);
                    v___x_2785_ = lean_array_get_borrowed(v___x_2780_, v_es_2779_, v_j_2784_);
                    crate::leanh::lean_dec(v_j_2784_);
                    match crate::leanh::lean_obj_tag(v___x_2785_) {
                        0 => {
                            v_key_2786_ = crate::leanh::lean_ctor_get(v___x_2785_, 0);
                            v___x_2787_ = l_Lean_instBEqExtraModUse_beq(v_x_2778_, v_key_2786_);
                            return v___x_2787_;
                        }
                        1 => {
                            v_node_2788_ = crate::leanh::lean_ctor_get(v___x_2785_, 0);
                            v___x_2789_ = lean_usize_shift_right(v_x_2777_, v___x_2781_);
                            v_x_2776_ = v_node_2788_;
                            v_x_2777_ = v___x_2789_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2791_ = 0;
                            return v___x_2791_;
                        }
                    }
                } else {
                    v_ks_2792_ = crate::leanh::lean_ctor_get(v_x_2776_, 0);
                    v___x_2793_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2794_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4_spec__7___redArg(v_ks_2792_, v___x_2793_, v_x_2778_);
                    return v___x_2794_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_x_2795_: *mut crate::leanh::LeanObject,
    mut v_x_2796_: *mut crate::leanh::LeanObject,
    mut v_x_2797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_6256__boxed_2798_: usize = 0;
    let mut v_res_2799_: u8 = 0;
    let mut v_r_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_6256__boxed_2798_ = crate::leanh::lean_unbox_usize(v_x_2796_);
    crate::leanh::lean_dec(v_x_2796_);
    v_res_2799_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg(v_x_2795_, v_x_6256__boxed_2798_, v_x_2797_);
    crate::leanh::lean_dec_ref(v_x_2797_);
    crate::leanh::lean_dec_ref(v_x_2795_);
    v_r_2800_ = crate::leanh::lean_box((v_res_2799_) as usize);
    return v_r_2800_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(
    mut v_x_2801_: *mut crate::leanh::LeanObject,
    mut v_x_2802_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2803_: u64 = 0;
    let mut v___x_2804_: usize = 0;
    let mut v___x_2805_: u8 = 0;
    v___x_2803_ = l_Lean_instHashableExtraModUse_hash(v_x_2802_);
    v___x_2804_ = lean_uint64_to_usize(v___x_2803_);
    v___x_2805_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg(v_x_2801_, v___x_2804_, v_x_2802_);
    return v___x_2805_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___boxed(
    mut v_x_2806_: *mut crate::leanh::LeanObject,
    mut v_x_2807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2808_: u8 = 0;
    let mut v_r_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2808_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v_x_2806_, v_x_2807_);
    crate::leanh::lean_dec_ref(v_x_2807_);
    crate::leanh::lean_dec_ref(v_x_2806_);
    v_r_2809_ = crate::leanh::lean_box((v_res_2808_) as usize);
    return v_r_2809_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2812_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__1;
    v___x_2813_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__0;
    v___x_2814_ = l_Lean_PersistentHashMap_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2813_,
        v___x_2812_,
    );
    return v___x_2814_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2819_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__5;
    v___x_2820_ = l_Lean_stringToMessageData(v___x_2819_);
    return v___x_2820_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2822_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__7;
    v___x_2823_ = l_Lean_stringToMessageData(v___x_2822_);
    return v___x_2823_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2824_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___closed__1;
    v___x_2825_ = l_Lean_stringToMessageData(v___x_2824_);
    return v___x_2825_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v_cls_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cls_2829_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__4;
    v___x_2830_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__11;
    v___x_2831_ = l_Lean_Name_append(v___x_2830_, v_cls_2829_);
    return v___x_2831_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2833_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__13;
    v___x_2834_ = l_Lean_stringToMessageData(v___x_2833_);
    return v___x_2834_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2836_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__15;
    v___x_2837_ = l_Lean_stringToMessageData(v___x_2836_);
    return v___x_2837_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1(
    mut v_mod_2842_: *mut crate::leanh::LeanObject,
    mut v_isMeta_2843_: u8,
    mut v_hint_2844_: *mut crate::leanh::LeanObject,
    mut v___y_2845_: *mut crate::leanh::LeanObject,
    mut v___y_2846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_2850_: u8 = 0;
    let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2872_: u8 = 0;
    let mut v_asyncMode_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2882_: u8 = 0;
    let mut v_unused_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: u8 = 0;
    let mut v_options_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2887_: u8 = 0;
    let mut v_inheritedTraceOptions_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: u8 = 0;
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: u8 = 0;
    let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2848_ = lean_st_ref_get(v___y_2846_);
                v_env_2849_ = crate::leanh::lean_ctor_get(v___x_2848_, 0);
                crate::leanh::lean_inc_ref(v_env_2849_);
                crate::leanh::lean_dec(v___x_2848_);
                v_isExporting_2850_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_2849_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                crate::leanh::lean_dec_ref(v_env_2849_);
                v___x_2851_ = lean_st_ref_get(v___y_2846_);
                v_env_2852_ = crate::leanh::lean_ctor_get(v___x_2851_, 0);
                crate::leanh::lean_inc_ref(v_env_2852_);
                crate::leanh::lean_dec(v___x_2851_);
                v___x_2853_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__2);
                crate::leanh::lean_inc(v_mod_2842_);
                v_entry_2854_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                crate::leanh::lean_ctor_set(v_entry_2854_, 0, v_mod_2842_);
                crate::leanh::lean_ctor_set_uint8(
                    v_entry_2854_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_isExporting_2850_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_entry_2854_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    v_isMeta_2843_,
                );
                v___x_2855_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_2856_ = crate::leanh::lean_box(1);
                v___x_2857_ = crate::leanh::lean_box(0);
                v___x_2884_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_2853_,
                    v___x_2855_,
                    v_env_2852_,
                    v___x_2856_,
                    v___x_2857_,
                );
                v___x_2885_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v___x_2884_, v_entry_2854_);
                crate::leanh::lean_dec(v___x_2884_);
                if v___x_2885_ == 0 {
                    v_options_2886_ = crate::leanh::lean_ctor_get(v___y_2845_, 2);
                    v_hasTrace_2887_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_2886_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_2887_ == 0 {
                        crate::leanh::lean_dec(v_hint_2844_);
                        crate::leanh::lean_dec(v_mod_2842_);
                        v___y_2859_ = v___y_2846_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_2888_ =
                            crate::leanh::lean_ctor_get(v___y_2845_, 13);
                        v_cls_2889_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__4;
                        v___x_2909_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__12);
                        v___x_2910_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_2888_,
                            v_options_2886_,
                            v___x_2909_,
                        );
                        if v___x_2910_ == 0 {
                            crate::leanh::lean_dec(v_hint_2844_);
                            crate::leanh::lean_dec(v_mod_2842_);
                            v___y_2859_ = v___y_2846_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2911_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__14_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__14);
                            if v_isExporting_2850_ == 0 {
                                v___x_2920_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__19;
                                v___y_2913_ = v___x_2920_;
                                state = 6;
                                continue;
                            } else {
                                v___x_2921_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__20;
                                v___y_2913_ = v___x_2921_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_entry_2854_, 1);
                    crate::leanh::lean_dec(v_hint_2844_);
                    crate::leanh::lean_dec(v_mod_2842_);
                    v___x_2922_ = crate::leanh::lean_box(0);
                    v___x_2923_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2923_, 0, v___x_2922_);
                    return v___x_2923_;
                }
            }
            1 => {
                v___x_2860_ = lean_st_ref_take(v___y_2859_);
                v_toEnvExtension_2861_ = crate::leanh::lean_ctor_get(v___x_2855_, 0);
                v_env_2862_ = crate::leanh::lean_ctor_get(v___x_2860_, 0);
                v_nextMacroScope_2863_ = crate::leanh::lean_ctor_get(v___x_2860_, 1);
                v_ngen_2864_ = crate::leanh::lean_ctor_get(v___x_2860_, 2);
                v_auxDeclNGen_2865_ = crate::leanh::lean_ctor_get(v___x_2860_, 3);
                v_traceState_2866_ = crate::leanh::lean_ctor_get(v___x_2860_, 4);
                v_messages_2867_ = crate::leanh::lean_ctor_get(v___x_2860_, 6);
                v_infoState_2868_ = crate::leanh::lean_ctor_get(v___x_2860_, 7);
                v_snapshotTasks_2869_ = crate::leanh::lean_ctor_get(v___x_2860_, 8);
                v_isSharedCheck_2882_ = (!crate::leanh::lean_is_exclusive(v___x_2860_)) as u8;
                if v_isSharedCheck_2882_ == 0 {
                    v_unused_2883_ = crate::leanh::lean_ctor_get(v___x_2860_, 5);
                    crate::leanh::lean_dec(v_unused_2883_);
                    v___x_2871_ = v___x_2860_;
                    v_isShared_2872_ = v_isSharedCheck_2882_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2869_);
                    crate::leanh::lean_inc(v_infoState_2868_);
                    crate::leanh::lean_inc(v_messages_2867_);
                    crate::leanh::lean_inc(v_traceState_2866_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2865_);
                    crate::leanh::lean_inc(v_ngen_2864_);
                    crate::leanh::lean_inc(v_nextMacroScope_2863_);
                    crate::leanh::lean_inc(v_env_2862_);
                    crate::leanh::lean_dec(v___x_2860_);
                    v___x_2871_ = crate::leanh::lean_box(0);
                    v_isShared_2872_ = v_isSharedCheck_2882_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_2873_ = crate::leanh::lean_ctor_get(v_toEnvExtension_2861_, 2);
                v___x_2874_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_2855_,
                    v_env_2862_,
                    v_entry_2854_,
                    v_asyncMode_2873_,
                    v___x_2857_,
                );
                v___x_2875_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_);
                if v_isShared_2872_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2871_, 5, v___x_2875_);
                    crate::leanh::lean_ctor_set(v___x_2871_, 0, v___x_2874_);
                    v___x_2877_ = v___x_2871_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2881_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2881_, 0, v___x_2874_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2881_, 1, v_nextMacroScope_2863_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2881_, 2, v_ngen_2864_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2881_, 3, v_auxDeclNGen_2865_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2881_, 4, v_traceState_2866_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2881_, 5, v___x_2875_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2881_, 6, v_messages_2867_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2881_, 7, v_infoState_2868_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2881_, 8, v_snapshotTasks_2869_);
                    v___x_2877_ = v_reuseFailAlloc_2881_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2878_ = lean_st_ref_set(v___y_2859_, v___x_2877_);
                v___x_2879_ = crate::leanh::lean_box(0);
                v___x_2880_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2880_, 0, v___x_2879_);
                return v___x_2880_;
            }
            4 => {
                v___x_2893_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2893_, 0, v___y_2891_);
                crate::leanh::lean_ctor_set(v___x_2893_, 1, v___y_2892_);
                v___x_2894_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3(v_cls_2889_, v___x_2893_, v___y_2845_, v___y_2846_);
                if crate::leanh::lean_obj_tag(v___x_2894_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2894_, 1);
                    v___y_2859_ = v___y_2846_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_entry_2854_, 1);
                    return v___x_2894_;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref(v___y_2897_);
                v___x_2898_ = l_Lean_stringToMessageData(v___y_2897_);
                v___x_2899_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2899_, 0, v___y_2896_);
                crate::leanh::lean_ctor_set(v___x_2899_, 1, v___x_2898_);
                v___x_2900_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__6), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__6_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__6);
                v___x_2901_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2901_, 0, v___x_2899_);
                crate::leanh::lean_ctor_set(v___x_2901_, 1, v___x_2900_);
                v___x_2902_ = l_Lean_MessageData_ofName(v_mod_2842_);
                v___x_2903_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2903_, 0, v___x_2901_);
                crate::leanh::lean_ctor_set(v___x_2903_, 1, v___x_2902_);
                v___x_2904_ = l_Lean_Name_isAnonymous(v_hint_2844_);
                if v___x_2904_ == 0 {
                    v___x_2905_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__8), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__8_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__8);
                    v___x_2906_ = l_Lean_MessageData_ofName(v_hint_2844_);
                    v___x_2907_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2907_, 0, v___x_2905_);
                    crate::leanh::lean_ctor_set(v___x_2907_, 1, v___x_2906_);
                    v___y_2891_ = v___x_2903_;
                    v___y_2892_ = v___x_2907_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_hint_2844_);
                    v___x_2908_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__9), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__9_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__9);
                    v___y_2891_ = v___x_2903_;
                    v___y_2892_ = v___x_2908_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                crate::leanh::lean_inc_ref(v___y_2913_);
                v___x_2914_ = l_Lean_stringToMessageData(v___y_2913_);
                v___x_2915_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2915_, 0, v___x_2911_);
                crate::leanh::lean_ctor_set(v___x_2915_, 1, v___x_2914_);
                v___x_2916_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__16), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__16_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__16);
                v___x_2917_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2917_, 0, v___x_2915_);
                crate::leanh::lean_ctor_set(v___x_2917_, 1, v___x_2916_);
                if v_isMeta_2843_ == 0 {
                    v___x_2918_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__17;
                    v___y_2896_ = v___x_2917_;
                    v___y_2897_ = v___x_2918_;
                    state = 5;
                    continue;
                } else {
                    v___x_2919_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__18;
                    v___y_2896_ = v___x_2917_;
                    v___y_2897_ = v___x_2919_;
                    state = 5;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___boxed(
    mut v_mod_2924_: *mut crate::leanh::LeanObject,
    mut v_isMeta_2925_: *mut crate::leanh::LeanObject,
    mut v_hint_2926_: *mut crate::leanh::LeanObject,
    mut v___y_2927_: *mut crate::leanh::LeanObject,
    mut v___y_2928_: *mut crate::leanh::LeanObject,
    mut v___y_2929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMeta_boxed_2930_: u8 = 0;
    let mut v_res_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_2930_ = (crate::leanh::lean_unbox(v_isMeta_2925_) as u8);
    v_res_2931_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1(v_mod_2924_, v_isMeta_boxed_2930_, v_hint_2926_, v___y_2927_, v___y_2928_);
    crate::leanh::lean_dec(v___y_2928_);
    crate::leanh::lean_dec_ref(v___y_2927_);
    return v_res_2931_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3_spec__6___redArg(
    mut v_a_2932_: *mut crate::leanh::LeanObject,
    mut v_x_2933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: u8 = 0;
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2933_) == 0 {
                    v___x_2934_ = crate::leanh::lean_box(0);
                    return v___x_2934_;
                } else {
                    v_key_2935_ = crate::leanh::lean_ctor_get(v_x_2933_, 0);
                    v_value_2936_ = crate::leanh::lean_ctor_get(v_x_2933_, 1);
                    v_tail_2937_ = crate::leanh::lean_ctor_get(v_x_2933_, 2);
                    v___x_2938_ = lean_name_eq(v_key_2935_, v_a_2932_);
                    if v___x_2938_ == 0 {
                        v_x_2933_ = v_tail_2937_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_2936_);
                        v___x_2940_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2940_, 0, v_value_2936_);
                        return v___x_2940_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3_spec__6___redArg___boxed(
    mut v_a_2941_: *mut crate::leanh::LeanObject,
    mut v_x_2942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2943_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3_spec__6___redArg(v_a_2941_, v_x_2942_);
    crate::leanh::lean_dec(v_x_2942_);
    crate::leanh::lean_dec(v_a_2941_);
    return v_res_2943_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg___closed__0()
-> u64 {
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: u64 = 0;
    v___x_2944_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_2945_ = lean_uint64_of_nat(v___x_2944_);
    return v___x_2945_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg(
    mut v_m_2946_: *mut crate::leanh::LeanObject,
    mut v_a_2947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2951_: u64 = 0;
    let mut v___x_2952_: u64 = 0;
    let mut v___x_2953_: u64 = 0;
    let mut v_fold_2954_: u64 = 0;
    let mut v___x_2955_: u64 = 0;
    let mut v___x_2956_: u64 = 0;
    let mut v___x_2957_: u64 = 0;
    let mut v___x_2958_: usize = 0;
    let mut v___x_2959_: usize = 0;
    let mut v___x_2960_: usize = 0;
    let mut v___x_2961_: usize = 0;
    let mut v___x_2962_: usize = 0;
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: u64 = 0;
    let mut v_hash_2966_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2948_ = crate::leanh::lean_ctor_get(v_m_2946_, 1);
                v___x_2949_ = lean_array_get_size(v_buckets_2948_);
                if crate::leanh::lean_obj_tag(v_a_2947_) == 0 {
                    v___x_2965_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg___closed__0);
                    v___y_2951_ = v___x_2965_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2966_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_2947_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2951_ = v_hash_2966_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2952_ = 32u64;
                v___x_2953_ = lean_uint64_shift_right(v___y_2951_, v___x_2952_);
                v_fold_2954_ = lean_uint64_xor(v___y_2951_, v___x_2953_);
                v___x_2955_ = 16u64;
                v___x_2956_ = lean_uint64_shift_right(v_fold_2954_, v___x_2955_);
                v___x_2957_ = lean_uint64_xor(v_fold_2954_, v___x_2956_);
                v___x_2958_ = lean_uint64_to_usize(v___x_2957_);
                v___x_2959_ = lean_usize_of_nat(v___x_2949_);
                v___x_2960_ = 1usize;
                v___x_2961_ = lean_usize_sub(v___x_2959_, v___x_2960_);
                v___x_2962_ = lean_usize_land(v___x_2958_, v___x_2961_);
                v___x_2963_ = lean_array_uget_borrowed(v_buckets_2948_, v___x_2962_);
                v___x_2964_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3_spec__6___redArg(v_a_2947_, v___x_2963_);
                return v___x_2964_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg___boxed(
    mut v_m_2967_: *mut crate::leanh::LeanObject,
    mut v_a_2968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2969_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg(v_m_2967_, v_a_2968_);
    crate::leanh::lean_dec(v_a_2968_);
    crate::leanh::lean_dec_ref(v_m_2967_);
    return v_res_2969_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__2(
    mut v___x_2970_: *mut crate::leanh::LeanObject,
    mut v_declName_2971_: *mut crate::leanh::LeanObject,
    mut v_as_2972_: *mut crate::leanh::LeanObject,
    mut v_sz_2973_: usize,
    mut v_i_2974_: usize,
    mut v_b_2975_: *mut crate::leanh::LeanObject,
    mut v___y_2976_: *mut crate::leanh::LeanObject,
    mut v___y_2977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2979_: u8 = 0;
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: u8 = 0;
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: usize = 0;
    let mut v___x_2992_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2979_ = lean_usize_dec_lt(v_i_2974_, v_sz_2973_);
                if v___x_2979_ == 0 {
                    crate::leanh::lean_dec(v_declName_2971_);
                    v___x_2980_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2980_, 0, v_b_2975_);
                    return v___x_2980_;
                } else {
                    v___x_2981_ = l_Lean_Environment_header(v___x_2970_);
                    v_modules_2982_ = crate::leanh::lean_ctor_get(v___x_2981_, 3);
                    crate::leanh::lean_inc_ref(v_modules_2982_);
                    crate::leanh::lean_dec_ref(v___x_2981_);
                    v___x_2983_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_2984_ = lean_array_uget_borrowed(v_as_2972_, v_i_2974_);
                    v___x_2985_ = lean_array_get(v___x_2983_, v_modules_2982_, v_a_2984_);
                    crate::leanh::lean_dec_ref(v_modules_2982_);
                    v_toImport_2986_ = crate::leanh::lean_ctor_get(v___x_2985_, 0);
                    crate::leanh::lean_inc_ref(v_toImport_2986_);
                    crate::leanh::lean_dec(v___x_2985_);
                    v_module_2987_ = crate::leanh::lean_ctor_get(v_toImport_2986_, 0);
                    crate::leanh::lean_inc(v_module_2987_);
                    crate::leanh::lean_dec_ref(v_toImport_2986_);
                    v___x_2988_ = 0;
                    crate::leanh::lean_inc(v_declName_2971_);
                    v___x_2989_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1(v_module_2987_, v___x_2988_, v_declName_2971_, v___y_2976_, v___y_2977_);
                    if crate::leanh::lean_obj_tag(v___x_2989_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2989_, 1);
                        v___x_2990_ = crate::leanh::lean_box(0);
                        v___x_2991_ = 1usize;
                        v___x_2992_ = lean_usize_add(v_i_2974_, v___x_2991_);
                        v_i_2974_ = v___x_2992_;
                        v_b_2975_ = v___x_2990_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_declName_2971_);
                        return v___x_2989_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__2___boxed(
    mut v___x_2994_: *mut crate::leanh::LeanObject,
    mut v_declName_2995_: *mut crate::leanh::LeanObject,
    mut v_as_2996_: *mut crate::leanh::LeanObject,
    mut v_sz_2997_: *mut crate::leanh::LeanObject,
    mut v_i_2998_: *mut crate::leanh::LeanObject,
    mut v_b_2999_: *mut crate::leanh::LeanObject,
    mut v___y_3000_: *mut crate::leanh::LeanObject,
    mut v___y_3001_: *mut crate::leanh::LeanObject,
    mut v___y_3002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3003_: usize = 0;
    let mut v_i_boxed_3004_: usize = 0;
    let mut v_res_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3003_ = crate::leanh::lean_unbox_usize(v_sz_2997_);
    crate::leanh::lean_dec(v_sz_2997_);
    v_i_boxed_3004_ = crate::leanh::lean_unbox_usize(v_i_2998_);
    crate::leanh::lean_dec(v_i_2998_);
    v_res_3005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__2(v___x_2994_, v_declName_2995_, v_as_2996_, v_sz_boxed_3003_, v_i_boxed_3004_, v_b_2999_, v___y_3000_, v___y_3001_);
    crate::leanh::lean_dec(v___y_3001_);
    crate::leanh::lean_dec_ref(v___y_3000_);
    crate::leanh::lean_dec_ref(v_as_2996_);
    crate::leanh::lean_dec_ref(v___x_2994_);
    return v_res_3005_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3008_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__1;
    v___x_3009_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__0;
    v___x_3010_ = l_Std_HashMap_instInhabited(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_3009_,
        v___x_3008_,
    );
    return v___x_3010_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1(
    mut v_declName_3013_: *mut crate::leanh::LeanObject,
    mut v_isMeta_3014_: u8,
    mut v___y_3015_: *mut crate::leanh::LeanObject,
    mut v___y_3016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3026_: usize = 0;
    let mut v___x_3027_: usize = 0;
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3031_: u8 = 0;
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3035_: u8 = 0;
    let mut v_unused_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: u8 = 0;
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3048_: u8 = 0;
    let mut v_toImport_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: u8 = 0;
    let mut v___x_3060_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3018_ = lean_st_ref_get(v___y_3016_);
                v_env_3022_ = crate::leanh::lean_ctor_get(v___x_3018_, 0);
                crate::leanh::lean_inc_ref(v_env_3022_);
                crate::leanh::lean_dec(v___x_3018_);
                v___x_3037_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3022_, v_declName_3013_);
                if crate::leanh::lean_obj_tag(v___x_3037_) == 0 {
                    crate::leanh::lean_dec_ref(v_env_3022_);
                    crate::leanh::lean_dec(v_declName_3013_);
                    state = 1;
                    continue;
                } else {
                    v_val_3038_ = crate::leanh::lean_ctor_get(v___x_3037_, 0);
                    crate::leanh::lean_inc(v_val_3038_);
                    crate::leanh::lean_dec_ref_known(v___x_3037_, 1);
                    v___x_3039_ = l_Lean_Environment_header(v_env_3022_);
                    v_modules_3040_ = crate::leanh::lean_ctor_get(v___x_3039_, 3);
                    crate::leanh::lean_inc_ref(v_modules_3040_);
                    crate::leanh::lean_dec_ref(v___x_3039_);
                    v___x_3041_ = lean_array_get_size(v_modules_3040_);
                    v___x_3042_ = lean_nat_dec_lt(v_val_3038_, v___x_3041_);
                    if v___x_3042_ == 0 {
                        crate::leanh::lean_dec_ref(v_modules_3040_);
                        crate::leanh::lean_dec(v_val_3038_);
                        crate::leanh::lean_dec_ref(v_env_3022_);
                        crate::leanh::lean_dec(v_declName_3013_);
                        state = 1;
                        continue;
                    } else {
                        v___x_3043_ = lean_st_ref_get(v___y_3016_);
                        v_env_3044_ = crate::leanh::lean_ctor_get(v___x_3043_, 0);
                        crate::leanh::lean_inc_ref(v_env_3044_);
                        crate::leanh::lean_dec(v___x_3043_);
                        v___x_3045_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__2);
                        v___x_3046_ = lean_array_fget(v_modules_3040_, v_val_3038_);
                        crate::leanh::lean_dec(v_val_3038_);
                        crate::leanh::lean_dec_ref(v_modules_3040_);
                        if v_isMeta_3014_ == 0 {
                            crate::leanh::lean_dec_ref(v_env_3044_);
                            v___y_3048_ = v_isMeta_3014_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_declName_3013_);
                            v___x_3059_ = l_Lean_isMarkedMeta(v_env_3044_, v_declName_3013_);
                            if v___x_3059_ == 0 {
                                v___y_3048_ = v_isMeta_3014_;
                                state = 5;
                                continue;
                            } else {
                                v___x_3060_ = 0;
                                v___y_3048_ = v___x_3060_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3020_ = crate::leanh::lean_box(0);
                v___x_3021_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3021_, 0, v___x_3020_);
                return v___x_3021_;
            }
            2 => {
                v___x_3025_ = crate::leanh::lean_box(0);
                v_sz_3026_ = lean_array_size(v___y_3024_);
                v___x_3027_ = 0usize;
                v___x_3028_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__2(v_env_3022_, v_declName_3013_, v___y_3024_, v_sz_3026_, v___x_3027_, v___x_3025_, v___y_3015_, v___y_3016_);
                crate::leanh::lean_dec_ref(v___y_3024_);
                crate::leanh::lean_dec_ref(v_env_3022_);
                if crate::leanh::lean_obj_tag(v___x_3028_) == 0 {
                    v_isSharedCheck_3035_ = (!crate::leanh::lean_is_exclusive(v___x_3028_)) as u8;
                    if v_isSharedCheck_3035_ == 0 {
                        v_unused_3036_ = crate::leanh::lean_ctor_get(v___x_3028_, 0);
                        crate::leanh::lean_dec(v_unused_3036_);
                        v___x_3030_ = v___x_3028_;
                        v_isShared_3031_ = v_isSharedCheck_3035_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3028_);
                        v___x_3030_ = crate::leanh::lean_box(0);
                        v_isShared_3031_ = v_isSharedCheck_3035_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_3028_;
                }
            }
            3 => {
                if v_isShared_3031_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3030_, 0, v___x_3025_);
                    v___x_3033_ = v___x_3030_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3034_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3034_, 0, v___x_3025_);
                    v___x_3033_ = v_reuseFailAlloc_3034_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3033_;
            }
            5 => {
                v_toImport_3049_ = crate::leanh::lean_ctor_get(v___x_3046_, 0);
                crate::leanh::lean_inc_ref(v_toImport_3049_);
                crate::leanh::lean_dec(v___x_3046_);
                v_module_3050_ = crate::leanh::lean_ctor_get(v_toImport_3049_, 0);
                crate::leanh::lean_inc(v_module_3050_);
                crate::leanh::lean_dec_ref(v_toImport_3049_);
                crate::leanh::lean_inc(v_declName_3013_);
                v___x_3051_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1(v_module_3050_, v___y_3048_, v_declName_3013_, v___y_3015_, v___y_3016_);
                if crate::leanh::lean_obj_tag(v___x_3051_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3051_, 1);
                    v___x_3052_ = l_Lean_indirectModUseExt;
                    v___x_3053_ = crate::leanh::lean_box(1);
                    v___x_3054_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_env_3022_);
                    v___x_3055_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_3045_,
                        v___x_3052_,
                        v_env_3022_,
                        v___x_3053_,
                        v___x_3054_,
                    );
                    v___x_3056_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg(v___x_3055_, v_declName_3013_);
                    crate::leanh::lean_dec(v___x_3055_);
                    if crate::leanh::lean_obj_tag(v___x_3056_) == 0 {
                        v___x_3057_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__3;
                        v___y_3024_ = v___x_3057_;
                        state = 2;
                        continue;
                    } else {
                        v_val_3058_ = crate::leanh::lean_ctor_get(v___x_3056_, 0);
                        crate::leanh::lean_inc(v_val_3058_);
                        crate::leanh::lean_dec_ref_known(v___x_3056_, 1);
                        v___y_3024_ = v_val_3058_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_3022_);
                    crate::leanh::lean_dec(v_declName_3013_);
                    return v___x_3051_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___boxed(
    mut v_declName_3061_: *mut crate::leanh::LeanObject,
    mut v_isMeta_3062_: *mut crate::leanh::LeanObject,
    mut v___y_3063_: *mut crate::leanh::LeanObject,
    mut v___y_3064_: *mut crate::leanh::LeanObject,
    mut v___y_3065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMeta_boxed_3066_: u8 = 0;
    let mut v_res_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_3066_ = (crate::leanh::lean_unbox(v_isMeta_3062_) as u8);
    v_res_3067_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1(v_declName_3061_, v_isMeta_boxed_3066_, v___y_3063_, v___y_3064_);
    crate::leanh::lean_dec(v___y_3064_);
    crate::leanh::lean_dec_ref(v___y_3063_);
    return v_res_3067_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__2(
    mut v___y_3068_: u8,
    mut v_as_3069_: *mut crate::leanh::LeanObject,
    mut v_i_3070_: usize,
    mut v_stop_3071_: usize,
    mut v_b_3072_: *mut crate::leanh::LeanObject,
    mut v___y_3073_: *mut crate::leanh::LeanObject,
    mut v___y_3074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3076_: u8 = 0;
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: usize = 0;
    let mut v___x_3081_: usize = 0;
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3076_ = lean_usize_dec_eq(v_i_3070_, v_stop_3071_);
                if v___x_3076_ == 0 {
                    v___x_3077_ = lean_array_uget_borrowed(v_as_3069_, v_i_3070_);
                    crate::leanh::lean_inc(v___x_3077_);
                    v___x_3078_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1(v___x_3077_, v___y_3068_, v___y_3073_, v___y_3074_);
                    if crate::leanh::lean_obj_tag(v___x_3078_) == 0 {
                        v_a_3079_ = crate::leanh::lean_ctor_get(v___x_3078_, 0);
                        crate::leanh::lean_inc(v_a_3079_);
                        crate::leanh::lean_dec_ref_known(v___x_3078_, 1);
                        v___x_3080_ = 1usize;
                        v___x_3081_ = lean_usize_add(v_i_3070_, v___x_3080_);
                        v_i_3070_ = v___x_3081_;
                        v_b_3072_ = v_a_3079_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3078_;
                    }
                } else {
                    v___x_3083_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3083_, 0, v_b_3072_);
                    return v___x_3083_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__2___boxed(
    mut v___y_3084_: *mut crate::leanh::LeanObject,
    mut v_as_3085_: *mut crate::leanh::LeanObject,
    mut v_i_3086_: *mut crate::leanh::LeanObject,
    mut v_stop_3087_: *mut crate::leanh::LeanObject,
    mut v_b_3088_: *mut crate::leanh::LeanObject,
    mut v___y_3089_: *mut crate::leanh::LeanObject,
    mut v___y_3090_: *mut crate::leanh::LeanObject,
    mut v___y_3091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6748__boxed_3092_: u8 = 0;
    let mut v_i_boxed_3093_: usize = 0;
    let mut v_stop_boxed_3094_: usize = 0;
    let mut v_res_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_6748__boxed_3092_ = (crate::leanh::lean_unbox(v___y_3084_) as u8);
    v_i_boxed_3093_ = crate::leanh::lean_unbox_usize(v_i_3086_);
    crate::leanh::lean_dec(v_i_3086_);
    v_stop_boxed_3094_ = crate::leanh::lean_unbox_usize(v_stop_3087_);
    crate::leanh::lean_dec(v_stop_3087_);
    v_res_3095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__2(v___y_6748__boxed_3092_, v_as_3085_, v_i_boxed_3093_, v_stop_boxed_3094_, v_b_3088_, v___y_3089_, v___y_3090_);
    crate::leanh::lean_dec(v___y_3090_);
    crate::leanh::lean_dec_ref(v___y_3089_);
    crate::leanh::lean_dec_ref(v_as_3085_);
    return v_res_3095_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__0(
    mut v_sz_3096_: usize,
    mut v_i_3097_: usize,
    mut v_bs_3098_: *mut crate::leanh::LeanObject,
    mut v___y_3099_: *mut crate::leanh::LeanObject,
    mut v___y_3100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3102_: u8 = 0;
    let mut v___x_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: usize = 0;
    let mut v___x_3111_: usize = 0;
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3117_: u8 = 0;
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3121_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3102_ = lean_usize_dec_lt(v_i_3097_, v_sz_3096_);
                if v___x_3102_ == 0 {
                    v___x_3103_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3103_, 0, v_bs_3098_);
                    return v___x_3103_;
                } else {
                    v_v_3104_ = lean_array_uget_borrowed(v_bs_3098_, v_i_3097_);
                    v___x_3105_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_v_3104_);
                    v___x_3106_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(
                        v_v_3104_,
                        v___x_3105_,
                        v___y_3099_,
                        v___y_3100_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3106_) == 0 {
                        v_a_3107_ = crate::leanh::lean_ctor_get(v___x_3106_, 0);
                        crate::leanh::lean_inc(v_a_3107_);
                        crate::leanh::lean_dec_ref_known(v___x_3106_, 1);
                        v___x_3108_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_3109_ = lean_array_uset(v_bs_3098_, v_i_3097_, v___x_3108_);
                        v___x_3110_ = 1usize;
                        v___x_3111_ = lean_usize_add(v_i_3097_, v___x_3110_);
                        v___x_3112_ = lean_array_uset(v_bs_x27_3109_, v_i_3097_, v_a_3107_);
                        v_i_3097_ = v___x_3111_;
                        v_bs_3098_ = v___x_3112_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_3098_);
                        v_a_3114_ = crate::leanh::lean_ctor_get(v___x_3106_, 0);
                        v_isSharedCheck_3121_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3106_)) as u8;
                        if v_isSharedCheck_3121_ == 0 {
                            v___x_3116_ = v___x_3106_;
                            v_isShared_3117_ = v_isSharedCheck_3121_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3114_);
                            crate::leanh::lean_dec(v___x_3106_);
                            v___x_3116_ = crate::leanh::lean_box(0);
                            v_isShared_3117_ = v_isSharedCheck_3121_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3117_ == 0 {
                    v___x_3119_ = v___x_3116_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3120_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_a_3114_);
                    v___x_3119_ = v_reuseFailAlloc_3120_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3119_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__0___boxed(
    mut v_sz_3122_: *mut crate::leanh::LeanObject,
    mut v_i_3123_: *mut crate::leanh::LeanObject,
    mut v_bs_3124_: *mut crate::leanh::LeanObject,
    mut v___y_3125_: *mut crate::leanh::LeanObject,
    mut v___y_3126_: *mut crate::leanh::LeanObject,
    mut v___y_3127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3128_: usize = 0;
    let mut v_i_boxed_3129_: usize = 0;
    let mut v_res_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3128_ = crate::leanh::lean_unbox_usize(v_sz_3122_);
    crate::leanh::lean_dec(v_sz_3122_);
    v_i_boxed_3129_ = crate::leanh::lean_unbox_usize(v_i_3123_);
    crate::leanh::lean_dec(v_i_3123_);
    v_res_3130_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__0(v_sz_boxed_3128_, v_i_boxed_3129_, v_bs_3124_, v___y_3125_, v___y_3126_);
    crate::leanh::lean_dec(v___y_3126_);
    crate::leanh::lean_dec_ref(v___y_3125_);
    return v_res_3130_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_(
    mut v___x_3131_: *mut crate::leanh::LeanObject,
    mut v___x_3132_: *mut crate::leanh::LeanObject,
    mut v___x_3133_: *mut crate::leanh::LeanObject,
    mut v___x_3134_: *mut crate::leanh::LeanObject,
    mut v___x_3135_: *mut crate::leanh::LeanObject,
    mut v_decl_3136_: *mut crate::leanh::LeanObject,
    mut v_stx_3137_: *mut crate::leanh::LeanObject,
    mut v_kind_3138_: u8,
    mut v___y_3139_: *mut crate::leanh::LeanObject,
    mut v___y_3140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3155_: u8 = 0;
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3167_: u8 = 0;
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3183_: u8 = 0;
    let mut v_unused_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3185_: u8 = 0;
    let mut v_a_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3189_: u8 = 0;
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3197_: u8 = 0;
    let mut v___y_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3206_: usize = 0;
    let mut v___y_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3208_: u8 = 0;
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: u8 = 0;
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: u8 = 0;
    let mut v___x_3213_: usize = 0;
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: usize = 0;
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3221_: u8 = 0;
    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: u8 = 0;
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3231_: usize = 0;
    let mut v___x_3232_: usize = 0;
    let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3237_: u8 = 0;
    let mut v___x_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: u8 = 0;
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3246_: u8 = 0;
    let mut v_a_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3250_: u8 = 0;
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3254_: u8 = 0;
    let mut v_isSharedCheck_3255_: u8 = 0;
    let mut v_unused_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: u8 = 0;
    let mut v___x_3258_: u8 = 0;
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3257_ = 0;
                v___x_3258_ = l_Lean_instBEqAttributeKind_beq(v_kind_3138_, v___x_3257_);
                if v___x_3258_ == 0 {
                    crate::leanh::lean_dec(v_stx_3137_);
                    crate::leanh::lean_dec(v_decl_3136_);
                    crate::leanh::lean_dec_ref(v___x_3135_);
                    crate::leanh::lean_dec_ref(v___x_3134_);
                    crate::leanh::lean_dec(v___x_3131_);
                    v___x_3259_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg(v___x_3133_, v_kind_3138_, v___y_3139_, v___y_3140_);
                    return v___x_3259_;
                } else {
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_3146_ = lean_st_ref_get(v___y_3144_);
                v_env_3147_ = crate::leanh::lean_ctor_get(v___x_3146_, 0);
                crate::leanh::lean_inc_ref(v_env_3147_);
                crate::leanh::lean_dec(v___x_3146_);
                v_options_3148_ = crate::leanh::lean_ctor_get(v___y_3143_, 2);
                v_ref_3149_ = crate::leanh::lean_ctor_get(v___y_3143_, 5);
                crate::leanh::lean_inc_ref(v_options_3148_);
                v___x_3150_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3150_, 0, v_env_3147_);
                crate::leanh::lean_ctor_set(v___x_3150_, 1, v_options_3148_);
                crate::leanh::lean_inc(v_decl_3136_);
                v___x_3151_ = l_Lean_CodeAction_mkCommandCodeAction(v_decl_3136_, v___x_3150_);
                crate::leanh::lean_dec_ref_known(v___x_3150_, 2);
                if crate::leanh::lean_obj_tag(v___x_3151_) == 0 {
                    v_a_3152_ = crate::leanh::lean_ctor_get(v___x_3151_, 0);
                    v_isSharedCheck_3185_ = (!crate::leanh::lean_is_exclusive(v___x_3151_)) as u8;
                    if v_isSharedCheck_3185_ == 0 {
                        v___x_3154_ = v___x_3151_;
                        v_isShared_3155_ = v_isSharedCheck_3185_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3152_);
                        crate::leanh::lean_dec(v___x_3151_);
                        v___x_3154_ = crate::leanh::lean_box(0);
                        v_isShared_3155_ = v_isSharedCheck_3185_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_3145_);
                    crate::leanh::lean_dec(v_decl_3136_);
                    crate::leanh::lean_dec(v___x_3131_);
                    v_a_3186_ = crate::leanh::lean_ctor_get(v___x_3151_, 0);
                    v_isSharedCheck_3197_ = (!crate::leanh::lean_is_exclusive(v___x_3151_)) as u8;
                    if v_isSharedCheck_3197_ == 0 {
                        v___x_3188_ = v___x_3151_;
                        v_isShared_3189_ = v_isSharedCheck_3197_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3186_);
                        crate::leanh::lean_dec(v___x_3151_);
                        v___x_3188_ = crate::leanh::lean_box(0);
                        v_isShared_3189_ = v_isSharedCheck_3197_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3156_ = lean_st_ref_take(v___y_3144_);
                v_env_3157_ = crate::leanh::lean_ctor_get(v___x_3156_, 0);
                v_nextMacroScope_3158_ = crate::leanh::lean_ctor_get(v___x_3156_, 1);
                v_ngen_3159_ = crate::leanh::lean_ctor_get(v___x_3156_, 2);
                v_auxDeclNGen_3160_ = crate::leanh::lean_ctor_get(v___x_3156_, 3);
                v_traceState_3161_ = crate::leanh::lean_ctor_get(v___x_3156_, 4);
                v_messages_3162_ = crate::leanh::lean_ctor_get(v___x_3156_, 6);
                v_infoState_3163_ = crate::leanh::lean_ctor_get(v___x_3156_, 7);
                v_snapshotTasks_3164_ = crate::leanh::lean_ctor_get(v___x_3156_, 8);
                v_isSharedCheck_3183_ = (!crate::leanh::lean_is_exclusive(v___x_3156_)) as u8;
                if v_isSharedCheck_3183_ == 0 {
                    v_unused_3184_ = crate::leanh::lean_ctor_get(v___x_3156_, 5);
                    crate::leanh::lean_dec(v_unused_3184_);
                    v___x_3166_ = v___x_3156_;
                    v_isShared_3167_ = v_isSharedCheck_3183_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3164_);
                    crate::leanh::lean_inc(v_infoState_3163_);
                    crate::leanh::lean_inc(v_messages_3162_);
                    crate::leanh::lean_inc(v_traceState_3161_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3160_);
                    crate::leanh::lean_inc(v_ngen_3159_);
                    crate::leanh::lean_inc(v_nextMacroScope_3158_);
                    crate::leanh::lean_inc(v_env_3157_);
                    crate::leanh::lean_dec(v___x_3156_);
                    v___x_3166_ = crate::leanh::lean_box(0);
                    v_isShared_3167_ = v_isSharedCheck_3183_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3168_ = l_Lean_CodeAction_cmdCodeActionExt;
                v_toEnvExtension_3169_ = crate::leanh::lean_ctor_get(v___x_3168_, 0);
                v_asyncMode_3170_ = crate::leanh::lean_ctor_get(v_toEnvExtension_3169_, 2);
                v___x_3171_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3171_, 0, v_decl_3136_);
                crate::leanh::lean_ctor_set(v___x_3171_, 1, v___y_3145_);
                v___x_3172_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3172_, 0, v___x_3171_);
                crate::leanh::lean_ctor_set(v___x_3172_, 1, v_a_3152_);
                v___x_3173_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_3168_,
                    v_env_3157_,
                    v___x_3172_,
                    v_asyncMode_3170_,
                    v___x_3131_,
                );
                v___x_3174_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_);
                if v_isShared_3167_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3166_, 5, v___x_3174_);
                    crate::leanh::lean_ctor_set(v___x_3166_, 0, v___x_3173_);
                    v___x_3176_ = v___x_3166_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3182_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3173_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3182_, 1, v_nextMacroScope_3158_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3182_, 2, v_ngen_3159_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3182_, 3, v_auxDeclNGen_3160_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3182_, 4, v_traceState_3161_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3182_, 5, v___x_3174_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3182_, 6, v_messages_3162_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3182_, 7, v_infoState_3163_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3182_, 8, v_snapshotTasks_3164_);
                    v___x_3176_ = v_reuseFailAlloc_3182_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3177_ = lean_st_ref_set(v___y_3144_, v___x_3176_);
                v___x_3178_ = crate::leanh::lean_box(0);
                if v_isShared_3155_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3154_, 0, v___x_3178_);
                    v___x_3180_ = v___x_3154_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3181_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3181_, 0, v___x_3178_);
                    v___x_3180_ = v_reuseFailAlloc_3181_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3180_;
            }
            6 => {
                v___x_3190_ = lean_io_error_to_string(v_a_3186_);
                v___x_3191_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3191_, 0, v___x_3190_);
                v___x_3192_ = l_Lean_MessageData_ofFormat(v___x_3191_);
                crate::leanh::lean_inc(v_ref_3149_);
                v___x_3193_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3193_, 0, v_ref_3149_);
                crate::leanh::lean_ctor_set(v___x_3193_, 1, v___x_3192_);
                if v_isShared_3189_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3188_, 0, v___x_3193_);
                    v___x_3195_ = v___x_3188_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3196_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3196_, 0, v___x_3193_);
                    v___x_3195_ = v_reuseFailAlloc_3196_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3195_;
            }
            8 => {
                if crate::leanh::lean_obj_tag(v___y_3202_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_3202_, 1);
                    v___y_3143_ = v___y_3199_;
                    v___y_3144_ = v___y_3200_;
                    v___y_3145_ = v___y_3201_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_3201_);
                    crate::leanh::lean_dec(v_decl_3136_);
                    crate::leanh::lean_dec(v___x_3131_);
                    return v___y_3202_;
                }
            }
            9 => {
                v___x_3209_ = lean_array_get_size(v___y_3207_);
                v___x_3210_ = lean_nat_dec_lt(v___x_3132_, v___x_3209_);
                if v___x_3210_ == 0 {
                    v___y_3143_ = v___y_3204_;
                    v___y_3144_ = v___y_3205_;
                    v___y_3145_ = v___y_3207_;
                    state = 1;
                    continue;
                } else {
                    v___x_3211_ = crate::leanh::lean_box(0);
                    v___x_3212_ = lean_nat_dec_le(v___x_3209_, v___x_3209_);
                    if v___x_3212_ == 0 {
                        if v___x_3210_ == 0 {
                            v___y_3143_ = v___y_3204_;
                            v___y_3144_ = v___y_3205_;
                            v___y_3145_ = v___y_3207_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3213_ = lean_usize_of_nat(v___x_3209_);
                            v___x_3214_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__2(v___y_3208_, v___y_3207_, v___y_3206_, v___x_3213_, v___x_3211_, v___y_3204_, v___y_3205_);
                            v___y_3199_ = v___y_3204_;
                            v___y_3200_ = v___y_3205_;
                            v___y_3201_ = v___y_3207_;
                            v___y_3202_ = v___x_3214_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v___x_3215_ = lean_usize_of_nat(v___x_3209_);
                        v___x_3216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__2(v___y_3208_, v___y_3207_, v___y_3206_, v___x_3215_, v___x_3211_, v___y_3204_, v___y_3205_);
                        v___y_3199_ = v___y_3204_;
                        v___y_3200_ = v___y_3205_;
                        v___y_3201_ = v___y_3207_;
                        v___y_3202_ = v___x_3216_;
                        state = 8;
                        continue;
                    }
                }
            }
            10 => {
                crate::leanh::lean_inc(v_decl_3136_);
                v___x_3218_ = l_Lean_ensureAttrDeclIsMeta(
                    v___x_3133_,
                    v_decl_3136_,
                    v_kind_3138_,
                    v___y_3139_,
                    v___y_3140_,
                );
                if crate::leanh::lean_obj_tag(v___x_3218_) == 0 {
                    v_isSharedCheck_3255_ = (!crate::leanh::lean_is_exclusive(v___x_3218_)) as u8;
                    if v_isSharedCheck_3255_ == 0 {
                        v_unused_3256_ = crate::leanh::lean_ctor_get(v___x_3218_, 0);
                        crate::leanh::lean_dec(v_unused_3256_);
                        v___x_3220_ = v___x_3218_;
                        v_isShared_3221_ = v_isSharedCheck_3255_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3218_);
                        v___x_3220_ = crate::leanh::lean_box(0);
                        v_isShared_3221_ = v_isSharedCheck_3255_;
                        state = 11;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_stx_3137_);
                    crate::leanh::lean_dec(v_decl_3136_);
                    crate::leanh::lean_dec_ref(v___x_3135_);
                    crate::leanh::lean_dec_ref(v___x_3134_);
                    crate::leanh::lean_dec(v___x_3131_);
                    return v___x_3218_;
                }
            }
            11 => {
                v___x_3222_ = l_Lean_Name_mkStr2(v___x_3134_, v___x_3135_);
                crate::leanh::lean_inc(v_stx_3137_);
                v___x_3223_ = l_Lean_Syntax_isOfKind(v_stx_3137_, v___x_3222_);
                crate::leanh::lean_dec(v___x_3222_);
                if v___x_3223_ == 0 {
                    crate::leanh::lean_dec(v_stx_3137_);
                    crate::leanh::lean_dec(v_decl_3136_);
                    crate::leanh::lean_dec(v___x_3131_);
                    v___x_3224_ = crate::leanh::lean_box(0);
                    if v_isShared_3221_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3220_, 0, v___x_3224_);
                        v___x_3226_ = v___x_3220_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_3227_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3227_, 0, v___x_3224_);
                        v___x_3226_ = v_reuseFailAlloc_3227_;
                        state = 12;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3220_);
                    v___x_3228_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3229_ = l_Lean_Syntax_getArg(v_stx_3137_, v___x_3228_);
                    crate::leanh::lean_dec(v_stx_3137_);
                    v___x_3230_ = l_Lean_Syntax_getArgs(v___x_3229_);
                    crate::leanh::lean_dec(v___x_3229_);
                    v_sz_3231_ = lean_array_size(v___x_3230_);
                    v___x_3232_ = 0usize;
                    v___x_3233_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__0(v_sz_3231_, v___x_3232_, v___x_3230_, v___y_3139_, v___y_3140_);
                    if crate::leanh::lean_obj_tag(v___x_3233_) == 0 {
                        v_a_3234_ = crate::leanh::lean_ctor_get(v___x_3233_, 0);
                        v_isSharedCheck_3246_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3233_)) as u8;
                        if v_isSharedCheck_3246_ == 0 {
                            v___x_3236_ = v___x_3233_;
                            v_isShared_3237_ = v_isSharedCheck_3246_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3234_);
                            crate::leanh::lean_dec(v___x_3233_);
                            v___x_3236_ = crate::leanh::lean_box(0);
                            v_isShared_3237_ = v_isSharedCheck_3246_;
                            state = 13;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_decl_3136_);
                        crate::leanh::lean_dec(v___x_3131_);
                        v_a_3247_ = crate::leanh::lean_ctor_get(v___x_3233_, 0);
                        v_isSharedCheck_3254_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3233_)) as u8;
                        if v_isSharedCheck_3254_ == 0 {
                            v___x_3249_ = v___x_3233_;
                            v_isShared_3250_ = v_isSharedCheck_3254_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3247_);
                            crate::leanh::lean_dec(v___x_3233_);
                            v___x_3249_ = crate::leanh::lean_box(0);
                            v_isShared_3250_ = v_isSharedCheck_3254_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            12 => {
                return v___x_3226_;
            }
            13 => {
                v___x_3238_ = lean_st_ref_get(v___y_3140_);
                v_env_3239_ = crate::leanh::lean_ctor_get(v___x_3238_, 0);
                crate::leanh::lean_inc_ref(v_env_3239_);
                crate::leanh::lean_dec(v___x_3238_);
                crate::leanh::lean_inc(v_decl_3136_);
                v___x_3240_ = lean_decl_get_sorry_dep(v_env_3239_, v_decl_3136_);
                if crate::leanh::lean_obj_tag(v___x_3240_) == 0 {
                    crate::leanh::lean_del_object(v___x_3236_);
                    v___x_3241_ = 0;
                    v___y_3204_ = v___y_3139_;
                    v___y_3205_ = v___y_3140_;
                    v___y_3206_ = v___x_3232_;
                    v___y_3207_ = v_a_3234_;
                    v___y_3208_ = v___x_3241_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_3240_, 1);
                    if v___x_3223_ == 0 {
                        crate::leanh::lean_del_object(v___x_3236_);
                        v___y_3204_ = v___y_3139_;
                        v___y_3205_ = v___y_3140_;
                        v___y_3206_ = v___x_3232_;
                        v___y_3207_ = v_a_3234_;
                        v___y_3208_ = v___x_3223_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_3234_);
                        crate::leanh::lean_dec(v_decl_3136_);
                        crate::leanh::lean_dec(v___x_3131_);
                        v___x_3242_ = crate::leanh::lean_box(0);
                        if v_isShared_3237_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3236_, 0, v___x_3242_);
                            v___x_3244_ = v___x_3236_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_3245_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3245_, 0, v___x_3242_);
                            v___x_3244_ = v_reuseFailAlloc_3245_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            14 => {
                return v___x_3244_;
            }
            15 => {
                if v_isShared_3250_ == 0 {
                    v___x_3252_ = v___x_3249_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3253_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_a_3247_);
                    v___x_3252_ = v_reuseFailAlloc_3253_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3252_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2____boxed(
    mut v___x_3260_: *mut crate::leanh::LeanObject,
    mut v___x_3261_: *mut crate::leanh::LeanObject,
    mut v___x_3262_: *mut crate::leanh::LeanObject,
    mut v___x_3263_: *mut crate::leanh::LeanObject,
    mut v___x_3264_: *mut crate::leanh::LeanObject,
    mut v_decl_3265_: *mut crate::leanh::LeanObject,
    mut v_stx_3266_: *mut crate::leanh::LeanObject,
    mut v_kind_3267_: *mut crate::leanh::LeanObject,
    mut v___y_3268_: *mut crate::leanh::LeanObject,
    mut v___y_3269_: *mut crate::leanh::LeanObject,
    mut v___y_3270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_3271_: u8 = 0;
    let mut v_res_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_3271_ = (crate::leanh::lean_unbox(v_kind_3267_) as u8);
    v_res_3272_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_(v___x_3260_, v___x_3261_, v___x_3262_, v___x_3263_, v___x_3264_, v_decl_3265_, v_stx_3266_, v_kind_boxed_3271_, v___y_3268_, v___y_3269_);
    crate::leanh::lean_dec(v___y_3269_);
    crate::leanh::lean_dec_ref(v___y_3268_);
    crate::leanh::lean_dec(v___x_3261_);
    return v_res_3272_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_(
    mut v___x_3273_: *mut crate::leanh::LeanObject,
    mut v_decl_3274_: *mut crate::leanh::LeanObject,
    mut v___y_3275_: *mut crate::leanh::LeanObject,
    mut v___y_3276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3278_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_);
    v___x_3279_ = l_Lean_MessageData_ofName(v___x_3273_);
    v___x_3280_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3280_, 0, v___x_3278_);
    crate::leanh::lean_ctor_set(v___x_3280_, 1, v___x_3279_);
    v___x_3281_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_);
    v___x_3282_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3282_, 0, v___x_3280_);
    crate::leanh::lean_ctor_set(v___x_3282_, 1, v___x_3281_);
    v___x_3283_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0___redArg(v___x_3282_, v___y_3275_, v___y_3276_);
    return v___x_3283_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2____boxed(
    mut v___x_3284_: *mut crate::leanh::LeanObject,
    mut v_decl_3285_: *mut crate::leanh::LeanObject,
    mut v___y_3286_: *mut crate::leanh::LeanObject,
    mut v___y_3287_: *mut crate::leanh::LeanObject,
    mut v___y_3288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3289_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_(v___x_3284_, v_decl_3285_, v___y_3286_, v___y_3287_);
    crate::leanh::lean_dec(v___y_3287_);
    crate::leanh::lean_dec_ref(v___y_3286_);
    crate::leanh::lean_dec(v_decl_3285_);
    return v_res_3289_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3324_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_;
    v___x_3325_ = l_Lean_registerBuiltinAttribute(v___x_3324_);
    return v___x_3325_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2____boxed(
    mut v_a_3326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3327_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_();
    return v_res_3327_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3(
    mut v_00_u03b2_3328_: *mut crate::leanh::LeanObject,
    mut v_m_3329_: *mut crate::leanh::LeanObject,
    mut v_a_3330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3331_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg(v_m_3329_, v_a_3330_);
    return v___x_3331_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___boxed(
    mut v_00_u03b2_3332_: *mut crate::leanh::LeanObject,
    mut v_m_3333_: *mut crate::leanh::LeanObject,
    mut v_a_3334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3335_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3(v_00_u03b2_3332_, v_m_3333_, v_a_3334_);
    crate::leanh::lean_dec(v_a_3334_);
    crate::leanh::lean_dec_ref(v_m_3333_);
    return v_res_3335_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2(
    mut v_00_u03b2_3336_: *mut crate::leanh::LeanObject,
    mut v_x_3337_: *mut crate::leanh::LeanObject,
    mut v_x_3338_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3339_: u8 = 0;
    v___x_3339_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v_x_3337_, v_x_3338_);
    return v___x_3339_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(
    mut v_00_u03b2_3340_: *mut crate::leanh::LeanObject,
    mut v_x_3341_: *mut crate::leanh::LeanObject,
    mut v_x_3342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3343_: u8 = 0;
    let mut v_r_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3343_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_00_u03b2_3340_, v_x_3341_, v_x_3342_);
    crate::leanh::lean_dec_ref(v_x_3342_);
    crate::leanh::lean_dec_ref(v_x_3341_);
    v_r_3344_ = crate::leanh::lean_box((v_res_3343_) as usize);
    return v_r_3344_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3_spec__6(
    mut v_00_u03b2_3345_: *mut crate::leanh::LeanObject,
    mut v_a_3346_: *mut crate::leanh::LeanObject,
    mut v_x_3347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3348_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3_spec__6___redArg(v_a_3346_, v_x_3347_);
    return v___x_3348_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3_spec__6___boxed(
    mut v_00_u03b2_3349_: *mut crate::leanh::LeanObject,
    mut v_a_3350_: *mut crate::leanh::LeanObject,
    mut v_x_3351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3352_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3_spec__6(v_00_u03b2_3349_, v_a_3350_, v_x_3351_);
    crate::leanh::lean_dec(v_x_3351_);
    crate::leanh::lean_dec(v_a_3350_);
    return v_res_3352_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4(
    mut v_00_u03b2_3353_: *mut crate::leanh::LeanObject,
    mut v_x_3354_: *mut crate::leanh::LeanObject,
    mut v_x_3355_: usize,
    mut v_x_3356_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3357_: u8 = 0;
    v___x_3357_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg(v_x_3354_, v_x_3355_, v_x_3356_);
    return v___x_3357_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b2_3358_: *mut crate::leanh::LeanObject,
    mut v_x_3359_: *mut crate::leanh::LeanObject,
    mut v_x_3360_: *mut crate::leanh::LeanObject,
    mut v_x_3361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_7272__boxed_3362_: usize = 0;
    let mut v_res_3363_: u8 = 0;
    let mut v_r_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_7272__boxed_3362_ = crate::leanh::lean_unbox_usize(v_x_3360_);
    crate::leanh::lean_dec(v_x_3360_);
    v_res_3363_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4(v_00_u03b2_3358_, v_x_3359_, v_x_7272__boxed_3362_, v_x_3361_);
    crate::leanh::lean_dec_ref(v_x_3361_);
    crate::leanh::lean_dec_ref(v_x_3359_);
    v_r_3364_ = crate::leanh::lean_box((v_res_3363_) as usize);
    return v_r_3364_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4_spec__7(
    mut v_00_u03b2_3365_: *mut crate::leanh::LeanObject,
    mut v_keys_3366_: *mut crate::leanh::LeanObject,
    mut v_vals_3367_: *mut crate::leanh::LeanObject,
    mut v_heq_3368_: *mut crate::leanh::LeanObject,
    mut v_i_3369_: *mut crate::leanh::LeanObject,
    mut v_k_3370_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3371_: u8 = 0;
    v___x_3371_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4_spec__7___redArg(v_keys_3366_, v_i_3369_, v_k_3370_);
    return v___x_3371_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4_spec__7___boxed(
    mut v_00_u03b2_3372_: *mut crate::leanh::LeanObject,
    mut v_keys_3373_: *mut crate::leanh::LeanObject,
    mut v_vals_3374_: *mut crate::leanh::LeanObject,
    mut v_heq_3375_: *mut crate::leanh::LeanObject,
    mut v_i_3376_: *mut crate::leanh::LeanObject,
    mut v_k_3377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3378_: u8 = 0;
    let mut v_r_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3378_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4_spec__7(v_00_u03b2_3372_, v_keys_3373_, v_vals_3374_, v_heq_3375_, v_i_3376_, v_k_3377_);
    crate::leanh::lean_dec_ref(v_k_3377_);
    crate::leanh::lean_dec_ref(v_vals_3374_);
    crate::leanh::lean_dec_ref(v_keys_3373_);
    v_r_3379_ = crate::leanh::lean_box((v_res_3378_) as usize);
    return v_r_3379_;
}
pub unsafe fn l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin_spec__0(
    mut v_nilFn_3380_: *mut crate::leanh::LeanObject,
    mut v_consFn_3381_: *mut crate::leanh::LeanObject,
    mut v_x_3382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3382_) == 0 {
        crate::leanh::lean_dec_ref(v_consFn_3381_);
        crate::leanh::lean_inc_ref(v_nilFn_3380_);
        return v_nilFn_3380_;
    } else {
        let mut v_head_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_3383_ = crate::leanh::lean_ctor_get(v_x_3382_, 0);
        crate::leanh::lean_inc(v_head_3383_);
        v_tail_3384_ = crate::leanh::lean_ctor_get(v_x_3382_, 1);
        crate::leanh::lean_inc(v_tail_3384_);
        crate::leanh::lean_dec_ref_known(v_x_3382_, 2);
        v___x_3385_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_head_3383_);
        crate::leanh::lean_inc_ref(v_consFn_3381_);
        v___x_3386_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin_spec__0(v_nilFn_3380_, v_consFn_3381_, v_tail_3384_);
        v___x_3387_ = l_Lean_mkAppB(v_consFn_3381_, v___x_3385_, v___x_3386_);
        return v___x_3387_;
    }
}
pub unsafe fn l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin_spec__0___boxed(
    mut v_nilFn_3388_: *mut crate::leanh::LeanObject,
    mut v_consFn_3389_: *mut crate::leanh::LeanObject,
    mut v_x_3390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3391_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin_spec__0(v_nilFn_3388_, v_consFn_3389_, v_x_3390_);
    crate::leanh::lean_dec_ref(v_nilFn_3388_);
    return v_res_3391_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3397_ = crate::leanh::lean_box(0);
    v___x_3398_ =
        l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__1;
    v___x_3399_ = l_Lean_mkConst(v___x_3398_, v___x_3397_);
    return v___x_3399_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3404_ = crate::leanh::lean_box(0);
    v___x_3405_ =
        l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__4;
    v_type_3406_ = l_Lean_mkConst(v___x_3405_, v___x_3404_);
    return v_type_3406_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3415_ =
        l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__9;
    v___x_3416_ =
        l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__8;
    v___x_3417_ = l_Lean_mkConst(v___x_3416_, v___x_3415_);
    return v___x_3417_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3418_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1);
    v___x_3419_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3419_, 0, v___x_3418_);
    crate::leanh::lean_ctor_set(v___x_3419_, 1, v___x_3418_);
    crate::leanh::lean_ctor_set(v___x_3419_, 2, v___x_3418_);
    crate::leanh::lean_ctor_set(v___x_3419_, 3, v___x_3418_);
    crate::leanh::lean_ctor_set(v___x_3419_, 4, v___x_3418_);
    crate::leanh::lean_ctor_set(v___x_3419_, 5, v___x_3418_);
    return v___x_3419_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3420_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3421_ = lean_mk_empty_array_with_capacity(v___x_3420_);
    v___x_3422_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3422_, 0, v___x_3421_);
    return v___x_3422_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3423_: usize = 0;
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3423_ = 5usize;
    v___x_3424_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3425_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3426_ = lean_mk_empty_array_with_capacity(v___x_3425_);
    v___x_3427_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__12_once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__12);
    v___x_3428_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_3428_, 0, v___x_3427_);
    crate::leanh::lean_ctor_set(v___x_3428_, 1, v___x_3426_);
    crate::leanh::lean_ctor_set(v___x_3428_, 2, v___x_3424_);
    crate::leanh::lean_ctor_set(v___x_3428_, 3, v___x_3424_);
    crate::leanh::lean_ctor_set_usize(v___x_3428_, 4, v___x_3423_);
    return v___x_3428_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3429_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1);
    v___x_3430_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3430_, 0, v___x_3429_);
    crate::leanh::lean_ctor_set(v___x_3430_, 1, v___x_3429_);
    crate::leanh::lean_ctor_set(v___x_3430_, 2, v___x_3429_);
    crate::leanh::lean_ctor_set(v___x_3430_, 3, v___x_3429_);
    crate::leanh::lean_ctor_set(v___x_3430_, 4, v___x_3429_);
    return v___x_3430_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3431_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__14_once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__14);
    v___x_3432_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__13_once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__13);
    v___x_3433_ = crate::leanh::lean_box(1);
    v___x_3434_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__11_once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__11);
    v___x_3435_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__2);
    v___x_3436_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3436_, 0, v___x_3435_);
    crate::leanh::lean_ctor_set(v___x_3436_, 1, v___x_3434_);
    crate::leanh::lean_ctor_set(v___x_3436_, 2, v___x_3433_);
    crate::leanh::lean_ctor_set(v___x_3436_, 3, v___x_3432_);
    crate::leanh::lean_ctor_set(v___x_3436_, 4, v___x_3431_);
    return v___x_3436_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3444_ =
        l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__9;
    v___x_3445_ =
        l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__19;
    v___x_3446_ = l_Lean_mkConst(v___x_3445_, v___x_3444_);
    return v___x_3446_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v_type_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nil_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_type_3447_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5_once
        ),
        _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5,
    );
    v___x_3448_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__20), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__20_once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__20);
    v_nil_3449_ = l_Lean_Expr_app___override(v___x_3448_, v_type_3447_);
    return v_nil_3449_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3454_ =
        l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__9;
    v___x_3455_ =
        l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__23;
    v___x_3456_ = l_Lean_mkConst(v___x_3455_, v___x_3454_);
    return v___x_3456_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v_type_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cons_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_type_3457_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5_once
        ),
        _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5,
    );
    v___x_3458_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__24), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__24_once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__24);
    v_cons_3459_ = l_Lean_Expr_app___override(v___x_3458_, v_type_3457_);
    return v_cons_3459_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin(
    mut v_declName_3460_: *mut crate::leanh::LeanObject,
    mut v_args_3461_: *mut crate::leanh::LeanObject,
    mut v_a_3462_: *mut crate::leanh::LeanObject,
    mut v_a_3463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nil_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cons_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3490_: u8 = 0;
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3495_: u8 = 0;
    let mut v_a_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3499_: u8 = 0;
    let mut v___x_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3503_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3465_ = crate::leanh::lean_box(0);
                v___x_3466_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__2_once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__2);
                v_type_3467_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5_once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5);
                v___x_3468_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__10_once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__10);
                v___x_3469_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__15_once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__15);
                v___x_3470_ = lean_st_mk_ref(v___x_3469_);
                crate::leanh::lean_inc(v_declName_3460_);
                v___x_3471_ = l_Lean_mkConst(v_declName_3460_, v___x_3465_);
                v___x_3472_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__17;
                v___x_3473_ = l_Lean_Name_append(v_declName_3460_, v___x_3472_);
                v___x_3474_ = l_Lean_Core_mkFreshUserName(v___x_3473_, v_a_3462_, v_a_3463_);
                if crate::leanh::lean_obj_tag(v___x_3474_) == 0 {
                    v_a_3475_ = crate::leanh::lean_ctor_get(v___x_3474_, 0);
                    crate::leanh::lean_inc(v_a_3475_);
                    crate::leanh::lean_dec_ref_known(v___x_3474_, 1);
                    v_nil_3476_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__21), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__21_once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__21);
                    v_cons_3477_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__25), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__25_once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__25);
                    v___x_3478_ = lean_array_to_list(v_args_3461_);
                    v___x_3479_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin_spec__0(v_nil_3476_, v_cons_3477_, v___x_3478_);
                    v___x_3480_ = l_Lean_mkAppB(v___x_3468_, v_type_3467_, v___x_3479_);
                    v___x_3481_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_3482_ = lean_mk_empty_array_with_capacity(v___x_3481_);
                    v___x_3483_ = lean_array_push(v___x_3482_, v___x_3480_);
                    v___x_3484_ = lean_array_push(v___x_3483_, v___x_3471_);
                    v_val_3485_ = l_Lean_mkAppN(v___x_3466_, v___x_3484_);
                    crate::leanh::lean_dec_ref(v___x_3484_);
                    v___x_3486_ =
                        l_Lean_declareBuiltin(v_a_3475_, v_val_3485_, v_a_3462_, v_a_3463_);
                    if crate::leanh::lean_obj_tag(v___x_3486_) == 0 {
                        v_a_3487_ = crate::leanh::lean_ctor_get(v___x_3486_, 0);
                        v_isSharedCheck_3495_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3486_)) as u8;
                        if v_isSharedCheck_3495_ == 0 {
                            v___x_3489_ = v___x_3486_;
                            v_isShared_3490_ = v_isSharedCheck_3495_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3487_);
                            crate::leanh::lean_dec(v___x_3486_);
                            v___x_3489_ = crate::leanh::lean_box(0);
                            v_isShared_3490_ = v_isSharedCheck_3495_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3470_);
                        return v___x_3486_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3471_);
                    crate::leanh::lean_dec(v___x_3470_);
                    crate::leanh::lean_dec_ref(v_args_3461_);
                    v_a_3496_ = crate::leanh::lean_ctor_get(v___x_3474_, 0);
                    v_isSharedCheck_3503_ = (!crate::leanh::lean_is_exclusive(v___x_3474_)) as u8;
                    if v_isSharedCheck_3503_ == 0 {
                        v___x_3498_ = v___x_3474_;
                        v_isShared_3499_ = v_isSharedCheck_3503_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3496_);
                        crate::leanh::lean_dec(v___x_3474_);
                        v___x_3498_ = crate::leanh::lean_box(0);
                        v_isShared_3499_ = v_isSharedCheck_3503_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3491_ = lean_st_ref_get(v___x_3470_);
                crate::leanh::lean_dec(v___x_3470_);
                crate::leanh::lean_dec(v___x_3491_);
                if v_isShared_3490_ == 0 {
                    v___x_3493_ = v___x_3489_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3494_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_a_3487_);
                    v___x_3493_ = v_reuseFailAlloc_3494_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3493_;
            }
            3 => {
                if v_isShared_3499_ == 0 {
                    v___x_3501_ = v___x_3498_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3502_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_a_3496_);
                    v___x_3501_ = v_reuseFailAlloc_3502_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3501_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___boxed(
    mut v_declName_3504_: *mut crate::leanh::LeanObject,
    mut v_args_3505_: *mut crate::leanh::LeanObject,
    mut v_a_3506_: *mut crate::leanh::LeanObject,
    mut v_a_3507_: *mut crate::leanh::LeanObject,
    mut v_a_3508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3509_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin(
        v_declName_3504_,
        v_args_3505_,
        v_a_3506_,
        v_a_3507_,
    );
    crate::leanh::lean_dec(v_a_3507_);
    crate::leanh::lean_dec_ref(v_a_3506_);
    return v_res_3509_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3511_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_;
    v___x_3512_ = l_Lean_stringToMessageData(v___x_3511_);
    return v___x_3512_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_(
    mut v___x_3513_: *mut crate::leanh::LeanObject,
    mut v___x_3514_: *mut crate::leanh::LeanObject,
    mut v_decl_3515_: *mut crate::leanh::LeanObject,
    mut v_stx_3516_: *mut crate::leanh::LeanObject,
    mut v_kind_3517_: u8,
    mut v___y_3518_: *mut crate::leanh::LeanObject,
    mut v___y_3519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: u8 = 0;
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3529_: usize = 0;
    let mut v___x_3530_: usize = 0;
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3535_: u8 = 0;
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3545_: u8 = 0;
    let mut v_a_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3549_: u8 = 0;
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3553_: u8 = 0;
    let mut v___x_3554_: u8 = 0;
    let mut v___x_3555_: u8 = 0;
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3554_ = 0;
                v___x_3555_ = l_Lean_instBEqAttributeKind_beq(v_kind_3517_, v___x_3554_);
                if v___x_3555_ == 0 {
                    crate::leanh::lean_dec(v_stx_3516_);
                    crate::leanh::lean_dec(v_decl_3515_);
                    crate::leanh::lean_dec_ref(v___x_3514_);
                    crate::leanh::lean_dec_ref(v___x_3513_);
                    v___x_3556_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_;
                    v___x_3557_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg(v___x_3556_, v_kind_3517_, v___y_3518_, v___y_3519_);
                    return v___x_3557_;
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3522_ = l_Lean_Name_mkStr2(v___x_3513_, v___x_3514_);
                crate::leanh::lean_inc(v_stx_3516_);
                v___x_3523_ = l_Lean_Syntax_isOfKind(v_stx_3516_, v___x_3522_);
                crate::leanh::lean_dec(v___x_3522_);
                if v___x_3523_ == 0 {
                    crate::leanh::lean_dec(v_stx_3516_);
                    crate::leanh::lean_dec(v_decl_3515_);
                    v___x_3524_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_);
                    v___x_3525_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0___redArg(v___x_3524_, v___y_3518_, v___y_3519_);
                    return v___x_3525_;
                } else {
                    v___x_3526_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3527_ = l_Lean_Syntax_getArg(v_stx_3516_, v___x_3526_);
                    crate::leanh::lean_dec(v_stx_3516_);
                    v_args_3528_ = l_Lean_Syntax_getArgs(v___x_3527_);
                    crate::leanh::lean_dec(v___x_3527_);
                    v_sz_3529_ = lean_array_size(v_args_3528_);
                    v___x_3530_ = 0usize;
                    v___x_3531_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__0(v_sz_3529_, v___x_3530_, v_args_3528_, v___y_3518_, v___y_3519_);
                    if crate::leanh::lean_obj_tag(v___x_3531_) == 0 {
                        v_a_3532_ = crate::leanh::lean_ctor_get(v___x_3531_, 0);
                        v_isSharedCheck_3545_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3531_)) as u8;
                        if v_isSharedCheck_3545_ == 0 {
                            v___x_3534_ = v___x_3531_;
                            v_isShared_3535_ = v_isSharedCheck_3545_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3532_);
                            crate::leanh::lean_dec(v___x_3531_);
                            v___x_3534_ = crate::leanh::lean_box(0);
                            v_isShared_3535_ = v_isSharedCheck_3545_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_decl_3515_);
                        v_a_3546_ = crate::leanh::lean_ctor_get(v___x_3531_, 0);
                        v_isSharedCheck_3553_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3531_)) as u8;
                        if v_isSharedCheck_3553_ == 0 {
                            v___x_3548_ = v___x_3531_;
                            v_isShared_3549_ = v_isSharedCheck_3553_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3546_);
                            crate::leanh::lean_dec(v___x_3531_);
                            v___x_3548_ = crate::leanh::lean_box(0);
                            v_isShared_3549_ = v_isSharedCheck_3553_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_3536_ = lean_st_ref_get(v___y_3519_);
                v_env_3537_ = crate::leanh::lean_ctor_get(v___x_3536_, 0);
                crate::leanh::lean_inc_ref(v_env_3537_);
                crate::leanh::lean_dec(v___x_3536_);
                crate::leanh::lean_inc(v_decl_3515_);
                v___x_3538_ = lean_decl_get_sorry_dep(v_env_3537_, v_decl_3515_);
                if crate::leanh::lean_obj_tag(v___x_3538_) == 0 {
                    crate::leanh::lean_del_object(v___x_3534_);
                    v___x_3539_ =
                        l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin(
                            v_decl_3515_,
                            v_a_3532_,
                            v___y_3518_,
                            v___y_3519_,
                        );
                    return v___x_3539_;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_3538_, 1);
                    if v___x_3523_ == 0 {
                        crate::leanh::lean_del_object(v___x_3534_);
                        v___x_3540_ =
                            l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin(
                                v_decl_3515_,
                                v_a_3532_,
                                v___y_3518_,
                                v___y_3519_,
                            );
                        return v___x_3540_;
                    } else {
                        crate::leanh::lean_dec(v_a_3532_);
                        crate::leanh::lean_dec(v_decl_3515_);
                        v___x_3541_ = crate::leanh::lean_box(0);
                        if v_isShared_3535_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3534_, 0, v___x_3541_);
                            v___x_3543_ = v___x_3534_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3544_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3544_, 0, v___x_3541_);
                            v___x_3543_ = v_reuseFailAlloc_3544_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_3543_;
            }
            4 => {
                if v_isShared_3549_ == 0 {
                    v___x_3551_ = v___x_3548_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3552_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_a_3546_);
                    v___x_3551_ = v_reuseFailAlloc_3552_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3551_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2____boxed(
    mut v___x_3558_: *mut crate::leanh::LeanObject,
    mut v___x_3559_: *mut crate::leanh::LeanObject,
    mut v_decl_3560_: *mut crate::leanh::LeanObject,
    mut v_stx_3561_: *mut crate::leanh::LeanObject,
    mut v_kind_3562_: *mut crate::leanh::LeanObject,
    mut v___y_3563_: *mut crate::leanh::LeanObject,
    mut v___y_3564_: *mut crate::leanh::LeanObject,
    mut v___y_3565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_3566_: u8 = 0;
    let mut v_res_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_3566_ = (crate::leanh::lean_unbox(v_kind_3562_) as u8);
    v_res_3567_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_(v___x_3558_, v___x_3559_, v_decl_3560_, v_stx_3561_, v_kind_boxed_3566_, v___y_3563_, v___y_3564_);
    crate::leanh::lean_dec(v___y_3564_);
    crate::leanh::lean_dec_ref(v___y_3563_);
    return v_res_3567_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3599_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_;
    v___x_3600_ = l_Lean_registerBuiltinAttribute(v___x_3599_);
    return v___x_3600_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2____boxed(
    mut v_a_3601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3602_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_();
    return v_res_3602_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_CodeActions_Attr(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Server_CodeActions_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_CodeAction_holeCodeActionExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_CodeAction_holeCodeActionExt);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_262607364____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_CodeAction_builtinCmdCodeActions = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_CodeAction_builtinCmdCodeActions);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_CodeAction_cmdCodeActionExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_CodeAction_cmdCodeActionExt);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_CodeActions_Attr(
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
pub unsafe fn initialize_Lean_Server_CodeActions_Attr(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Server_CodeActions_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_IR_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_CodeActions_Attr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_CodeActions_Attr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Server_CodeActions_Attr(builtin);
}
