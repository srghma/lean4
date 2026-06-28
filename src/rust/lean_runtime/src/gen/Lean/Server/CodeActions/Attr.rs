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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set,
    lean_ctor_set_float, lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64,
    lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object,
    lean_float_once, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_get_value,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat, lean_usize_once,
};
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__1_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__2_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [72, 111, 108, 101, 67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__1_value) as *mut LeanObject,1630946840184265901 as *mut LeanObject] };
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__2_value) as *mut LeanObject,15336260586967034768 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__2_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__3_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [104, 111, 108, 101, 67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 69, 120, 116, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__1_value) as *mut LeanObject,1630946840184265901 as *mut LeanObject] };
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut LeanObject,18169146760106986306 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value: LeanClosureObject<3> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__4_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 3, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value: LeanCtorObject<8> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*8 + 0) as u16, other: 8, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__11_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__11_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__11_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__0_value: LeanStringObject<38> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 115, 99, 111, 112, 101, 58, 32, 65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__2_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [93, 96, 32, 109, 117, 115, 116, 32, 98, 101, 32, 103, 108, 111, 98, 97, 108, 44, 32, 110, 111, 116, 32, 96, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__4_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__4_value) as *mut LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__6_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [103, 108, 111, 98, 97, 108, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__6_value) as *mut LeanObject;
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__7_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 111, 99, 97, 108, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__7_value) as *mut LeanObject;
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__8_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 99, 111, 112, 101, 100, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__8_value) as *mut LeanObject;
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 101, 114, 118, 101, 114, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,12337524736695414095 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,17302608593553616169 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [65, 116, 116, 114, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,9914264936907428297 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,1208168756163512716 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value) as *mut LeanObject,12060895093625083661 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__11_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__1_value) as *mut LeanObject,4737180066981367002 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__11_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__11_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__12_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__12_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__12_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__13_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__11_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__12_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,11048415496356105535 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__13_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__13_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__14_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__14_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__14_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__15_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__13_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__14_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,5775873084443761098 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__15_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__15_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__16_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__15_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value) as *mut LeanObject,16657014704763504075 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__16_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__16_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__17_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__16_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,9546742709096449002 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__17_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__17_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__18_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__17_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,10111873537814351968 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__18_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__18_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__19_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__18_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,2580783235213447324 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__19_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__19_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__20_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__19_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,((( 1824323934 as usize) << 1) | 1) as *mut LeanObject,13153020436653296944 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__20_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__20_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__21_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__21_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__21_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__22_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__20_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__21_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,18209967886157034215 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__22_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__22_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__23_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__23_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__23_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__24_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__22_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__23_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,11163147854334231087 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__24_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__24_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__25_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__24_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,18019106402232835370 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__25_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__25_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__26_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [104, 111, 108, 101, 95, 99, 111, 100, 101, 95, 97, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__26_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__26_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__27_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__26_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,11443572138440657403 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__27_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__27_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__28_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanClosureObject<2> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 8, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__27_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__28_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__28_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__29_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__27_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__29_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__29_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__30_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanStringObject<74> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 74, m_capacity: 74, m_length: 73, m_data: [68, 101, 99, 108, 97, 114, 101, 32, 97, 32, 110, 101, 119, 32, 104, 111, 108, 101, 32, 99, 111, 100, 101, 32, 97, 99, 116, 105, 111, 110, 44, 32, 116, 111, 32, 97, 112, 112, 101, 97, 114, 32, 105, 110, 32, 116, 104, 101, 32, 99, 111, 100, 101, 32, 97, 99, 116, 105, 111, 110, 115, 32, 111, 110, 32, 63, 95, 32, 97, 110, 100, 32, 95, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__30_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__30_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__31_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__25_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__27_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__30_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,1 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__31_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__31_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__32_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__31_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__28_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__29_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__32_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__32_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__0_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [67, 111, 109, 109, 97, 110, 100, 67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__1_value) as *mut LeanObject,1630946840184265901 as *mut LeanObject] };
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__0_value) as *mut LeanObject,15207379896936780160 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_CodeAction_instInhabitedCommandCodeActionEntry_default___closed__0_value:
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
static mut l_Lean_CodeAction_instInhabitedCommandCodeActionEntry_default___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_CodeAction_instInhabitedCommandCodeActionEntry_default___closed__0_value
) as *mut LeanObject;
pub static l_Lean_CodeAction_instInhabitedCommandCodeActionEntry_default___closed__1_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_CodeAction_instInhabitedCommandCodeActionEntry_default___closed__0_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lean_CodeAction_instInhabitedCommandCodeActionEntry_default___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_CodeAction_instInhabitedCommandCodeActionEntry_default___closed__1_value
) as *mut LeanObject;
pub static mut l_Lean_CodeAction_instInhabitedCommandCodeActionEntry_default: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_CodeAction_instInhabitedCommandCodeActionEntry_default___closed__1_value
)
    as *mut LeanObject;
pub static mut l_Lean_CodeAction_instInhabitedCommandCodeActionEntry: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_CodeAction_instInhabitedCommandCodeActionEntry_default___closed__1_value
)
    as *mut LeanObject;
pub static l_Lean_CodeAction_instInhabitedCommandCodeActions_default___closed__0_value:
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
static mut l_Lean_CodeAction_instInhabitedCommandCodeActions_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_instInhabitedCommandCodeActions_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_CodeAction_instInhabitedCommandCodeActions_default___closed__1_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_CodeAction_instInhabitedCommandCodeActions_default___closed__0_value
        ) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_CodeAction_instInhabitedCommandCodeActions_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_instInhabitedCommandCodeActions_default___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lean_CodeAction_instInhabitedCommandCodeActions_default: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_CodeAction_instInhabitedCommandCodeActions_default___closed__1_value
)
    as *mut LeanObject;
pub static mut l_Lean_CodeAction_instInhabitedCommandCodeActions: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_CodeAction_instInhabitedCommandCodeActions_default___closed__1_value
)
    as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_CommandCodeActions_insert_spec__1___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_CommandCodeActions_insert_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_CommandCodeActions_insert_spec__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__4___closed__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__4___closed__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__4___closed__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__2_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__3_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [99, 109, 100, 67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 69, 120, 116, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__1_value) as *mut LeanObject,1630946840184265901 as *mut LeanObject] };
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value) as *mut LeanObject,7373477140738405138 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___closed__2_value) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__1: usize = 0;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__3_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__3_value) as *mut LeanObject,7870113334857981723 as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__5_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__7_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__7_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__10_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__10_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__11_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__13_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__13_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__14_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__14: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__15_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__15_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__16_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__16: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__17_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__17_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__18_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__18_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__19_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__19_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__20_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__20_value) as *mut LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg___closed__0: u64 = 0;
pub static l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__1_value) as *mut LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__3_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__19_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,((( 249496773 as usize) << 1) | 1) as *mut LeanObject,10279444048633815591 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__21_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,17778551580831994572 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__23_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,3334465087617531768 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,17246597584702003577 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [99, 111, 109, 109, 97, 110, 100, 95, 99, 111, 100, 101, 95, 97, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut LeanObject,2488340241968920392 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value: LeanClosureObject<5> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*5) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 5, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value: LeanStringObject<77> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 77, m_capacity: 77, m_length: 76, m_data: [68, 101, 99, 108, 97, 114, 101, 32, 97, 32, 110, 101, 119, 32, 99, 111, 109, 109, 97, 110, 100, 32, 99, 111, 100, 101, 32, 97, 99, 116, 105, 111, 110, 44, 32, 116, 111, 32, 97, 112, 112, 101, 97, 114, 32, 105, 110, 32, 116, 104, 101, 32, 99, 111, 100, 101, 32, 97, 99, 116, 105, 111, 110, 115, 32, 111, 110, 32, 99, 111, 109, 109, 97, 110, 100, 115, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut LeanObject,1 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [105, 110, 115, 101, 114, 116, 66, 117, 105, 108, 116, 105, 110, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__0_value
) as *mut LeanObject;
static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__1_value) as *mut LeanObject,1630946840184265901 as *mut LeanObject] };
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__0_value) as *mut LeanObject,14351884860939696436 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__1_value
) as *mut LeanObject;
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [78, 97, 109, 101, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__3_value
) as *mut LeanObject;
static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__3_value) as *mut LeanObject,13306843946249674491 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__4_value
) as *mut LeanObject;
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__6_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 105, 115, 116, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__6_value
) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__7_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [116, 111, 65, 114, 114, 97, 121, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__7_value
) as *mut LeanObject;
static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__6_value) as *mut LeanObject,9582258842178272501 as *mut LeanObject] };
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__7_value) as *mut LeanObject,8414467900391110369 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__8_value
) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__9_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__9_value
) as *mut LeanObject;
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__10:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__11:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__12:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__13:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__14_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__14:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__15:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__16_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 101, 99, 108, 97, 114, 101, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__16:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__16_value
) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__16_value) as *mut LeanObject,13812150225987229964 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__17:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__17_value
) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__18_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 105, 108, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__18:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__18_value
) as *mut LeanObject;
static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__19_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__6_value) as *mut LeanObject,9582258842178272501 as *mut LeanObject] };
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__19_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__19_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__18_value) as *mut LeanObject,18135193680607614554 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__19:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__19_value
) as *mut LeanObject;
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__20_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__20:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__21_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__21:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__22_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 111, 110, 115, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__22:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__22_value
) as *mut LeanObject;
static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__23_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__6_value) as *mut LeanObject,9582258842178272501 as *mut LeanObject] };
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__23_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__23_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__22_value) as *mut LeanObject,8614124190858717794 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__23:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__23_value
) as *mut LeanObject;
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__24_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__24:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__25_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__25:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value: LeanStringObject<50> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 50, m_capacity: 50, m_length: 49, m_data: [85, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 96, 99, 111, 109, 109, 97, 110, 100, 95, 99, 111, 100, 101, 95, 97, 99, 116, 105, 111, 110, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 115, 121, 110, 116, 97, 120, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__19_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,((( 1324802641 as usize) << 1) | 1) as *mut LeanObject,9807269913042915022 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__21_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,4616878115496534297 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__23_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__value) as *mut LeanObject,3983418355711173073 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,14323203857448747948 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value: LeanStringObject<28> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 99, 111, 109, 109, 97, 110, 100, 95, 99, 111, 100, 101, 95, 97, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value: LeanClosureObject<2> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 8, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1___closed__0_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__4_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut LeanObject,5096520196538450623 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value: LeanStringObject<85> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 85, m_capacity: 85, m_length: 84, m_data: [68, 101, 99, 108, 97, 114, 101, 32, 97, 32, 110, 101, 119, 32, 98, 117, 105, 108, 116, 105, 110, 32, 99, 111, 109, 109, 97, 110, 100, 32, 99, 111, 100, 101, 32, 97, 99, 116, 105, 111, 110, 44, 32, 116, 111, 32, 97, 112, 112, 101, 97, 114, 32, 105, 110, 32, 116, 104, 101, 32, 99, 111, 100, 101, 32, 97, 99, 116, 105, 111, 110, 115, 32, 111, 110, 32, 99, 111, 109, 109, 97, 110, 100, 115, 0]};
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut LeanObject,1 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1(
    mut v_n_1809_: *mut LeanObject,
    mut v_env_1810_: *mut LeanObject,
    mut v_opts_1811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_n_1814_: *mut LeanObject,
    mut v_env_1815_: *mut LeanObject,
    mut v_opts_1816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1817_: *mut LeanObject = core::ptr::null_mut();
    v_res_1817_ =
        l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkHoleCodeAction_unsafe__1(
            v_n_1814_,
            v_env_1815_,
            v_opts_1816_,
        );
    lean_dec_ref(v_opts_1816_);
    return v_res_1817_;
}
pub unsafe fn l_IO_ofExcept___at___00Lean_CodeAction_mkHoleCodeAction_spec__0___redArg(
    mut v_e_1818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1823_: u8 = 0;
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1828_: u8 = 0;
    let mut v_a_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1832_: u8 = 0;
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1836_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_1818_) == 0 {
                    v_a_1820_ = lean_ctor_get(v_e_1818_, 0);
                    v_isSharedCheck_1828_ = (!lean_is_exclusive(v_e_1818_)) as u8;
                    if v_isSharedCheck_1828_ == 0 {
                        v___x_1822_ = v_e_1818_;
                        v_isShared_1823_ = v_isSharedCheck_1828_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1820_);
                        lean_dec(v_e_1818_);
                        v___x_1822_ = lean_box(0);
                        v_isShared_1823_ = v_isSharedCheck_1828_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1829_ = lean_ctor_get(v_e_1818_, 0);
                    v_isSharedCheck_1836_ = (!lean_is_exclusive(v_e_1818_)) as u8;
                    if v_isSharedCheck_1836_ == 0 {
                        v___x_1831_ = v_e_1818_;
                        v_isShared_1832_ = v_isSharedCheck_1836_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1829_);
                        lean_dec(v_e_1818_);
                        v___x_1831_ = lean_box(0);
                        v_isShared_1832_ = v_isSharedCheck_1836_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1824_ = lean_mk_io_user_error(v_a_1820_);
                if v_isShared_1823_ == 0 {
                    lean_ctor_set_tag(v___x_1822_, 1);
                    lean_ctor_set(v___x_1822_, 0, v___x_1824_);
                    v___x_1826_ = v___x_1822_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1824_);
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
                    lean_ctor_set_tag(v___x_1831_, 0);
                    v___x_1834_ = v___x_1831_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1829_);
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
    mut v_e_1837_: *mut LeanObject,
    mut v_a_1838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1839_: *mut LeanObject = core::ptr::null_mut();
    v_res_1839_ =
        l_IO_ofExcept___at___00Lean_CodeAction_mkHoleCodeAction_spec__0___redArg(v_e_1837_);
    return v_res_1839_;
}
pub unsafe fn l_IO_ofExcept___at___00Lean_CodeAction_mkHoleCodeAction_spec__0(
    mut v_00_u03b1_1840_: *mut LeanObject,
    mut v_e_1841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    v___x_1843_ =
        l_IO_ofExcept___at___00Lean_CodeAction_mkHoleCodeAction_spec__0___redArg(v_e_1841_);
    return v___x_1843_;
}
pub unsafe fn l_IO_ofExcept___at___00Lean_CodeAction_mkHoleCodeAction_spec__0___boxed(
    mut v_00_u03b1_1844_: *mut LeanObject,
    mut v_e_1845_: *mut LeanObject,
    mut v_a_1846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1847_: *mut LeanObject = core::ptr::null_mut();
    v_res_1847_ = l_IO_ofExcept___at___00Lean_CodeAction_mkHoleCodeAction_spec__0(
        v_00_u03b1_1844_,
        v_e_1845_,
    );
    return v_res_1847_;
}
pub unsafe fn l_Lean_CodeAction_mkHoleCodeAction(
    mut v_n_1848_: *mut LeanObject,
    mut v_a_1849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_env_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    v_env_1851_ = lean_ctor_get(v_a_1849_, 0);
    v_opts_1852_ = lean_ctor_get(v_a_1849_, 1);
    lean_inc_ref(v_env_1851_);
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
    mut v_n_1855_: *mut LeanObject,
    mut v_a_1856_: *mut LeanObject,
    mut v_a_1857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1858_: *mut LeanObject = core::ptr::null_mut();
    v_res_1858_ = l_Lean_CodeAction_mkHoleCodeAction(v_n_1855_, v_a_1856_);
    lean_dec_ref(v_a_1856_);
    return v_res_1858_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(
    mut v_x_1859_: *mut LeanObject,
    mut v_x_1860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1867_: u8 = 0;
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1873_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1861_ = lean_ctor_get(v_x_1859_, 0);
                lean_inc(v_fst_1861_);
                v_snd_1862_ = lean_ctor_get(v_x_1859_, 1);
                lean_inc(v_snd_1862_);
                lean_dec_ref(v_x_1859_);
                v_fst_1863_ = lean_ctor_get(v_x_1860_, 0);
                v_snd_1864_ = lean_ctor_get(v_x_1860_, 1);
                v_isSharedCheck_1873_ = (!lean_is_exclusive(v_x_1860_)) as u8;
                if v_isSharedCheck_1873_ == 0 {
                    v___x_1866_ = v_x_1860_;
                    v_isShared_1867_ = v_isSharedCheck_1873_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_1864_);
                    lean_inc(v_fst_1863_);
                    lean_dec(v_x_1860_);
                    v___x_1866_ = lean_box(0);
                    v_isShared_1867_ = v_isSharedCheck_1873_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1868_ = lean_array_push(v_fst_1861_, v_fst_1863_);
                v___x_1869_ = lean_array_push(v_snd_1862_, v_snd_1864_);
                if v_isShared_1867_ == 0 {
                    lean_ctor_set(v___x_1866_, 1, v___x_1869_);
                    lean_ctor_set(v___x_1866_, 0, v___x_1868_);
                    v___x_1871_ = v___x_1866_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1868_);
                    lean_ctor_set(v_reuseFailAlloc_1872_, 1, v___x_1869_);
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
    mut v_x_1874_: *mut LeanObject,
    mut v_s_1875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    v_fst_1876_ = lean_ctor_get(v_s_1875_, 0);
    lean_inc_n(v_fst_1876_, 3);
    v___x_1877_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1877_, 0, v_fst_1876_);
    lean_ctor_set(v___x_1877_, 1, v_fst_1876_);
    lean_ctor_set(v___x_1877_, 2, v_fst_1876_);
    return v___x_1877_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed(
    mut v_x_1878_: *mut LeanObject,
    mut v_s_1879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1880_: *mut LeanObject = core::ptr::null_mut();
    v_res_1880_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(v_x_1878_, v_s_1879_);
    lean_dec_ref(v_s_1879_);
    lean_dec_ref(v_x_1878_);
    return v_res_1880_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__2_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(
    mut v_x_1881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    v___x_1882_ = lean_box(0);
    return v___x_1882_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__2_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed(
    mut v_x_1883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1884_: *mut LeanObject = core::ptr::null_mut();
    v_res_1884_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__2_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(v_x_1883_);
    lean_dec_ref(v_x_1883_);
    return v_res_1884_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__3_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(
    mut v_x_1885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1886_: *mut LeanObject = core::ptr::null_mut();
    v_fst_1886_ = lean_ctor_get(v_x_1885_, 0);
    lean_inc(v_fst_1886_);
    return v_fst_1886_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__3_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed(
    mut v_x_1887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1888_: *mut LeanObject = core::ptr::null_mut();
    v_res_1888_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__3_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(v_x_1887_);
    lean_dec_ref(v_x_1887_);
    return v_res_1888_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__spec__0(
    mut v_as_1889_: *mut LeanObject,
    mut v_i_1890_: usize,
    mut v_stop_1891_: usize,
    mut v_b_1892_: *mut LeanObject,
    mut v___y_1893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1895_: u8 = 0;
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: usize = 0;
    let mut v___x_1901_: usize = 0;
    let mut v_a_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1906_: u8 = 0;
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1910_: u8 = 0;
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1895_ = lean_usize_dec_eq(v_i_1890_, v_stop_1891_);
                if v___x_1895_ == 0 {
                    v___x_1896_ = lean_array_uget_borrowed(v_as_1889_, v_i_1890_);
                    lean_inc(v___x_1896_);
                    v___x_1897_ = l_Lean_CodeAction_mkHoleCodeAction(v___x_1896_, v___y_1893_);
                    if lean_obj_tag(v___x_1897_) == 0 {
                        v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
                        lean_inc(v_a_1898_);
                        lean_dec_ref_known(v___x_1897_, 1);
                        v___x_1899_ = lean_array_push(v_b_1892_, v_a_1898_);
                        v___x_1900_ = 1usize;
                        v___x_1901_ = lean_usize_add(v_i_1890_, v___x_1900_);
                        v_i_1890_ = v___x_1901_;
                        v_b_1892_ = v___x_1899_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_b_1892_);
                        v_a_1903_ = lean_ctor_get(v___x_1897_, 0);
                        v_isSharedCheck_1910_ = (!lean_is_exclusive(v___x_1897_)) as u8;
                        if v_isSharedCheck_1910_ == 0 {
                            v___x_1905_ = v___x_1897_;
                            v_isShared_1906_ = v_isSharedCheck_1910_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1903_);
                            lean_dec(v___x_1897_);
                            v___x_1905_ = lean_box(0);
                            v_isShared_1906_ = v_isSharedCheck_1910_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_1911_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1911_, 0, v_b_1892_);
                    return v___x_1911_;
                }
            }
            1 => {
                if v_isShared_1906_ == 0 {
                    v___x_1908_ = v___x_1905_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
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
    mut v_as_1912_: *mut LeanObject,
    mut v_i_1913_: *mut LeanObject,
    mut v_stop_1914_: *mut LeanObject,
    mut v_b_1915_: *mut LeanObject,
    mut v___y_1916_: *mut LeanObject,
    mut v___y_1917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1918_: usize = 0;
    let mut v_stop_boxed_1919_: usize = 0;
    let mut v_res_1920_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1918_ = lean_unbox_usize(v_i_1913_);
    lean_dec(v_i_1913_);
    v_stop_boxed_1919_ = lean_unbox_usize(v_stop_1914_);
    lean_dec(v_stop_1914_);
    v_res_1920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__spec__0(v_as_1912_, v_i_boxed_1918_, v_stop_boxed_1919_, v_b_1915_, v___y_1916_);
    lean_dec_ref(v___y_1916_);
    lean_dec_ref(v_as_1912_);
    return v_res_1920_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__spec__1(
    mut v_as_1921_: *mut LeanObject,
    mut v_i_1922_: usize,
    mut v_stop_1923_: usize,
    mut v_b_1924_: *mut LeanObject,
    mut v___y_1925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: usize = 0;
    let mut v___x_1930_: usize = 0;
    let mut v___y_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: u8 = 0;
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: u8 = 0;
    let mut v___x_1940_: u8 = 0;
    let mut v___x_1941_: usize = 0;
    let mut v___x_1942_: usize = 0;
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: usize = 0;
    let mut v___x_1945_: usize = 0;
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1935_ = lean_usize_dec_eq(v_i_1922_, v_stop_1923_);
                if v___x_1935_ == 0 {
                    v___x_1936_ = lean_array_uget_borrowed(v_as_1921_, v_i_1922_);
                    v___x_1937_ = lean_unsigned_to_nat(0);
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
                    v___x_1947_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1947_, 0, v_b_1924_);
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
                if lean_obj_tag(v___y_1933_) == 0 {
                    v_a_1934_ = lean_ctor_get(v___y_1933_, 0);
                    lean_inc(v_a_1934_);
                    lean_dec_ref_known(v___y_1933_, 1);
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
    mut v_as_1948_: *mut LeanObject,
    mut v_i_1949_: *mut LeanObject,
    mut v_stop_1950_: *mut LeanObject,
    mut v_b_1951_: *mut LeanObject,
    mut v___y_1952_: *mut LeanObject,
    mut v___y_1953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1954_: usize = 0;
    let mut v_stop_boxed_1955_: usize = 0;
    let mut v_res_1956_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1954_ = lean_unbox_usize(v_i_1949_);
    lean_dec(v_i_1949_);
    v_stop_boxed_1955_ = lean_unbox_usize(v_stop_1950_);
    lean_dec(v_stop_1950_);
    v_res_1956_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2__spec__1(v_as_1948_, v_i_boxed_1954_, v_stop_boxed_1955_, v_b_1951_, v___y_1952_);
    lean_dec_ref(v___y_1952_);
    lean_dec_ref(v_as_1948_);
    return v_res_1956_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__4_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(
    mut v___x_1957_: *mut LeanObject,
    mut v___x_1958_: *mut LeanObject,
    mut v___x_1959_: *mut LeanObject,
    mut v_as_1960_: *mut LeanObject,
    mut v___y_1961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1973_: u8 = 0;
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1977_: u8 = 0;
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: u8 = 0;
    let mut v___x_1980_: u8 = 0;
    let mut v___x_1981_: usize = 0;
    let mut v___x_1982_: usize = 0;
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: usize = 0;
    let mut v___x_1985_: usize = 0;
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
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
                v___x_1965_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1965_, 0, v___x_1957_);
                lean_ctor_set(v___x_1965_, 1, v_a_1964_);
                v___x_1966_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1966_, 0, v___x_1965_);
                return v___x_1966_;
            }
            2 => {
                if lean_obj_tag(v___y_1968_) == 0 {
                    v_a_1969_ = lean_ctor_get(v___y_1968_, 0);
                    lean_inc(v_a_1969_);
                    lean_dec_ref_known(v___y_1968_, 1);
                    v_a_1964_ = v_a_1969_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v___x_1957_);
                    v_a_1970_ = lean_ctor_get(v___y_1968_, 0);
                    v_isSharedCheck_1977_ = (!lean_is_exclusive(v___y_1968_)) as u8;
                    if v_isSharedCheck_1977_ == 0 {
                        v___x_1972_ = v___y_1968_;
                        v_isShared_1973_ = v_isSharedCheck_1977_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1970_);
                        lean_dec(v___y_1968_);
                        v___x_1972_ = lean_box(0);
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
                    v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1970_);
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
    mut v___x_1987_: *mut LeanObject,
    mut v___x_1988_: *mut LeanObject,
    mut v___x_1989_: *mut LeanObject,
    mut v_as_1990_: *mut LeanObject,
    mut v___y_1991_: *mut LeanObject,
    mut v___y_1992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1993_: *mut LeanObject = core::ptr::null_mut();
    v_res_1993_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__4_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(v___x_1987_, v___x_1988_, v___x_1989_, v_as_1990_, v___y_1991_);
    lean_dec_ref(v___y_1991_);
    lean_dec_ref(v_as_1990_);
    lean_dec(v___x_1988_);
    return v_res_1993_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(
    mut v___x_1994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    v___x_1996_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1996_, 0, v___x_1994_);
    return v___x_1996_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed(
    mut v___x_1997_: *mut LeanObject,
    mut v___y_1998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1999_: *mut LeanObject = core::ptr::null_mut();
    v_res_1999_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__5_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_(v___x_1997_);
    return v_res_1999_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    v___x_2031_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__11_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_;
    v___x_2032_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2031_);
    return v___x_2032_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2____boxed(
    mut v_a_2033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2034_: *mut LeanObject = core::ptr::null_mut();
    v_res_2034_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_();
    return v_res_2034_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    v___x_2035_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2035_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    v___x_2036_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__0);
    v___x_2037_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2037_, 0, v___x_2036_);
    return v___x_2037_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    v___x_2038_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1);
    v___x_2039_ = lean_unsigned_to_nat(0);
    v___x_2040_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_2040_, 0, v___x_2039_);
    lean_ctor_set(v___x_2040_, 1, v___x_2039_);
    lean_ctor_set(v___x_2040_, 2, v___x_2039_);
    lean_ctor_set(v___x_2040_, 3, v___x_2039_);
    lean_ctor_set(v___x_2040_, 4, v___x_2038_);
    lean_ctor_set(v___x_2040_, 5, v___x_2038_);
    lean_ctor_set(v___x_2040_, 6, v___x_2038_);
    lean_ctor_set(v___x_2040_, 7, v___x_2038_);
    lean_ctor_set(v___x_2040_, 8, v___x_2038_);
    lean_ctor_set(v___x_2040_, 9, v___x_2038_);
    return v___x_2040_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    v___x_2041_ = lean_unsigned_to_nat(32);
    v___x_2042_ = lean_mk_empty_array_with_capacity(v___x_2041_);
    v___x_2043_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2043_, 0, v___x_2042_);
    return v___x_2043_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__4()
-> *mut LeanObject {
    let mut v___x_2044_: usize = 0;
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    v___x_2044_ = 5usize;
    v___x_2045_ = lean_unsigned_to_nat(0);
    v___x_2046_ = lean_unsigned_to_nat(32);
    v___x_2047_ = lean_mk_empty_array_with_capacity(v___x_2046_);
    v___x_2048_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__3);
    v___x_2049_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_2049_, 0, v___x_2048_);
    lean_ctor_set(v___x_2049_, 1, v___x_2047_);
    lean_ctor_set(v___x_2049_, 2, v___x_2045_);
    lean_ctor_set(v___x_2049_, 3, v___x_2045_);
    lean_ctor_set_usize(v___x_2049_, 4, v___x_2044_);
    return v___x_2049_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__5()
-> *mut LeanObject {
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    v___x_2050_ = lean_box(1);
    v___x_2051_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__4);
    v___x_2052_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1);
    v___x_2053_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2053_, 0, v___x_2052_);
    lean_ctor_set(v___x_2053_, 1, v___x_2051_);
    lean_ctor_set(v___x_2053_, 2, v___x_2050_);
    return v___x_2053_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0(
    mut v_msgData_2054_: *mut LeanObject,
    mut v___y_2055_: *mut LeanObject,
    mut v___y_2056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    v___x_2058_ = lean_st_ref_get(v___y_2056_);
    v_env_2059_ = lean_ctor_get(v___x_2058_, 0);
    lean_inc_ref(v_env_2059_);
    lean_dec(v___x_2058_);
    v_options_2060_ = lean_ctor_get(v___y_2055_, 2);
    v___x_2061_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__2);
    v___x_2062_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__5);
    lean_inc_ref(v_options_2060_);
    v___x_2063_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2063_, 0, v_env_2059_);
    lean_ctor_set(v___x_2063_, 1, v___x_2061_);
    lean_ctor_set(v___x_2063_, 2, v___x_2062_);
    lean_ctor_set(v___x_2063_, 3, v_options_2060_);
    v___x_2064_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2064_, 0, v___x_2063_);
    lean_ctor_set(v___x_2064_, 1, v_msgData_2054_);
    v___x_2065_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2065_, 0, v___x_2064_);
    return v___x_2065_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_msgData_2066_: *mut LeanObject,
    mut v___y_2067_: *mut LeanObject,
    mut v___y_2068_: *mut LeanObject,
    mut v___y_2069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2070_: *mut LeanObject = core::ptr::null_mut();
    v_res_2070_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0(v_msgData_2066_, v___y_2067_, v___y_2068_);
    lean_dec(v___y_2068_);
    lean_dec_ref(v___y_2067_);
    return v_res_2070_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0___redArg(
    mut v_msg_2071_: *mut LeanObject,
    mut v___y_2072_: *mut LeanObject,
    mut v___y_2073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2080_: u8 = 0;
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2085_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2075_ = lean_ctor_get(v___y_2072_, 5);
                v___x_2076_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0(v_msg_2071_, v___y_2072_, v___y_2073_);
                v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
                v_isSharedCheck_2085_ = (!lean_is_exclusive(v___x_2076_)) as u8;
                if v_isSharedCheck_2085_ == 0 {
                    v___x_2079_ = v___x_2076_;
                    v_isShared_2080_ = v_isSharedCheck_2085_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2077_);
                    lean_dec(v___x_2076_);
                    v___x_2079_ = lean_box(0);
                    v_isShared_2080_ = v_isSharedCheck_2085_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_2075_);
                v___x_2081_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2081_, 0, v_ref_2075_);
                lean_ctor_set(v___x_2081_, 1, v_a_2077_);
                if v_isShared_2080_ == 0 {
                    lean_ctor_set_tag(v___x_2079_, 1);
                    lean_ctor_set(v___x_2079_, 0, v___x_2081_);
                    v___x_2083_ = v___x_2079_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2081_);
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
    mut v_msg_2086_: *mut LeanObject,
    mut v___y_2087_: *mut LeanObject,
    mut v___y_2088_: *mut LeanObject,
    mut v___y_2089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2090_: *mut LeanObject = core::ptr::null_mut();
    v_res_2090_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0___redArg(v_msg_2086_, v___y_2087_, v___y_2088_);
    lean_dec(v___y_2088_);
    lean_dec_ref(v___y_2087_);
    return v_res_2090_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    v___x_2092_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__0;
    v___x_2093_ = l_Lean_stringToMessageData(v___x_2092_);
    return v___x_2093_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    v___x_2095_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__2;
    v___x_2096_ = l_Lean_stringToMessageData(v___x_2095_);
    return v___x_2096_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    v___x_2098_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__4;
    v___x_2099_ = l_Lean_stringToMessageData(v___x_2098_);
    return v___x_2099_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg(
    mut v_name_2103_: *mut LeanObject,
    mut v_kind_2104_: u8,
    mut v___y_2105_: *mut LeanObject,
    mut v___y_2106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2108_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__1_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__1);
                v___x_2109_ = l_Lean_MessageData_ofName(v_name_2103_);
                v___x_2110_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2110_, 0, v___x_2108_);
                lean_ctor_set(v___x_2110_, 1, v___x_2109_);
                v___x_2111_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__3_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__3);
                v___x_2112_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2112_, 0, v___x_2110_);
                lean_ctor_set(v___x_2112_, 1, v___x_2111_);
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
                lean_inc_ref(v___y_2114_);
                v___x_2115_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2115_, 0, v___y_2114_);
                v___x_2116_ = l_Lean_MessageData_ofFormat(v___x_2115_);
                v___x_2117_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2117_, 0, v___x_2112_);
                lean_ctor_set(v___x_2117_, 1, v___x_2116_);
                v___x_2118_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__5_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___closed__5);
                v___x_2119_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2119_, 0, v___x_2117_);
                lean_ctor_set(v___x_2119_, 1, v___x_2118_);
                v___x_2120_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0___redArg(v___x_2119_, v___y_2105_, v___y_2106_);
                return v___x_2120_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg___boxed(
    mut v_name_2124_: *mut LeanObject,
    mut v_kind_2125_: *mut LeanObject,
    mut v___y_2126_: *mut LeanObject,
    mut v___y_2127_: *mut LeanObject,
    mut v___y_2128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_2129_: u8 = 0;
    let mut v_res_2130_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_2129_ = (lean_unbox(v_kind_2125_) as u8);
    v_res_2130_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg(v_name_2124_, v_kind_boxed_2129_, v___y_2126_, v___y_2127_);
    lean_dec(v___y_2127_);
    lean_dec_ref(v___y_2126_);
    return v_res_2130_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    v___x_2131_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2131_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    v___x_2132_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_);
    v___x_2133_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2133_, 0, v___x_2132_);
    return v___x_2133_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    v___x_2134_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_);
    v___x_2135_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2135_, 0, v___x_2134_);
    lean_ctor_set(v___x_2135_, 1, v___x_2134_);
    return v___x_2135_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_(
    mut v___x_2136_: *mut LeanObject,
    mut v___x_2137_: *mut LeanObject,
    mut v_decl_2138_: *mut LeanObject,
    mut v_stx_2139_: *mut LeanObject,
    mut v_kind_2140_: u8,
    mut v___y_2141_: *mut LeanObject,
    mut v___y_2142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2150_: u8 = 0;
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2163_: u8 = 0;
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2175_: u8 = 0;
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2190_: u8 = 0;
    let mut v_unused_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2192_: u8 = 0;
    let mut v_a_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2196_: u8 = 0;
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2204_: u8 = 0;
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2209_: u8 = 0;
    let mut v_unused_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: u8 = 0;
    let mut v___x_2213_: u8 = 0;
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2211_ =
                    l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2139_, v___y_2141_, v___y_2142_);
                if lean_obj_tag(v___x_2211_) == 0 {
                    lean_dec_ref_known(v___x_2211_, 1);
                    v___x_2212_ = 0;
                    v___x_2213_ = l_Lean_instBEqAttributeKind_beq(v_kind_2140_, v___x_2212_);
                    if v___x_2213_ == 0 {
                        lean_dec(v_decl_2138_);
                        lean_dec(v___x_2137_);
                        v___x_2214_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg(v___x_2136_, v_kind_2140_, v___y_2141_, v___y_2142_);
                        return v___x_2214_;
                    } else {
                        v___y_2145_ = v___y_2141_;
                        v___y_2146_ = v___y_2142_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_decl_2138_);
                    lean_dec(v___x_2137_);
                    lean_dec(v___x_2136_);
                    return v___x_2211_;
                }
            }
            1 => {
                lean_inc(v_decl_2138_);
                v___x_2147_ = l_Lean_ensureAttrDeclIsMeta(
                    v___x_2136_,
                    v_decl_2138_,
                    v_kind_2140_,
                    v___y_2145_,
                    v___y_2146_,
                );
                if lean_obj_tag(v___x_2147_) == 0 {
                    v_isSharedCheck_2209_ = (!lean_is_exclusive(v___x_2147_)) as u8;
                    if v_isSharedCheck_2209_ == 0 {
                        v_unused_2210_ = lean_ctor_get(v___x_2147_, 0);
                        lean_dec(v_unused_2210_);
                        v___x_2149_ = v___x_2147_;
                        v_isShared_2150_ = v_isSharedCheck_2209_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_2147_);
                        v___x_2149_ = lean_box(0);
                        v_isShared_2150_ = v_isSharedCheck_2209_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_decl_2138_);
                    lean_dec(v___x_2137_);
                    return v___x_2147_;
                }
            }
            2 => {
                v___x_2151_ = lean_st_ref_get(v___y_2146_);
                v_env_2152_ = lean_ctor_get(v___x_2151_, 0);
                lean_inc_ref(v_env_2152_);
                lean_dec(v___x_2151_);
                lean_inc(v_decl_2138_);
                v___x_2153_ = lean_decl_get_sorry_dep(v_env_2152_, v_decl_2138_);
                if lean_obj_tag(v___x_2153_) == 0 {
                    lean_del_object(v___x_2149_);
                    v___x_2154_ = lean_st_ref_get(v___y_2146_);
                    v_env_2155_ = lean_ctor_get(v___x_2154_, 0);
                    lean_inc_ref(v_env_2155_);
                    lean_dec(v___x_2154_);
                    v_options_2156_ = lean_ctor_get(v___y_2145_, 2);
                    v_ref_2157_ = lean_ctor_get(v___y_2145_, 5);
                    lean_inc_ref(v_options_2156_);
                    v___x_2158_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2158_, 0, v_env_2155_);
                    lean_ctor_set(v___x_2158_, 1, v_options_2156_);
                    lean_inc(v_decl_2138_);
                    v___x_2159_ = l_Lean_CodeAction_mkHoleCodeAction(v_decl_2138_, v___x_2158_);
                    lean_dec_ref_known(v___x_2158_, 2);
                    if lean_obj_tag(v___x_2159_) == 0 {
                        v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
                        v_isSharedCheck_2192_ = (!lean_is_exclusive(v___x_2159_)) as u8;
                        if v_isSharedCheck_2192_ == 0 {
                            v___x_2162_ = v___x_2159_;
                            v_isShared_2163_ = v_isSharedCheck_2192_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2160_);
                            lean_dec(v___x_2159_);
                            v___x_2162_ = lean_box(0);
                            v_isShared_2163_ = v_isSharedCheck_2192_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_decl_2138_);
                        lean_dec(v___x_2137_);
                        v_a_2193_ = lean_ctor_get(v___x_2159_, 0);
                        v_isSharedCheck_2204_ = (!lean_is_exclusive(v___x_2159_)) as u8;
                        if v_isSharedCheck_2204_ == 0 {
                            v___x_2195_ = v___x_2159_;
                            v_isShared_2196_ = v_isSharedCheck_2204_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_2193_);
                            lean_dec(v___x_2159_);
                            v___x_2195_ = lean_box(0);
                            v_isShared_2196_ = v_isSharedCheck_2204_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref_known(v___x_2153_, 1);
                    lean_dec(v_decl_2138_);
                    lean_dec(v___x_2137_);
                    v___x_2205_ = lean_box(0);
                    if v_isShared_2150_ == 0 {
                        lean_ctor_set(v___x_2149_, 0, v___x_2205_);
                        v___x_2207_ = v___x_2149_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2205_);
                        v___x_2207_ = v_reuseFailAlloc_2208_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2164_ = lean_st_ref_take(v___y_2146_);
                v_env_2165_ = lean_ctor_get(v___x_2164_, 0);
                v_nextMacroScope_2166_ = lean_ctor_get(v___x_2164_, 1);
                v_ngen_2167_ = lean_ctor_get(v___x_2164_, 2);
                v_auxDeclNGen_2168_ = lean_ctor_get(v___x_2164_, 3);
                v_traceState_2169_ = lean_ctor_get(v___x_2164_, 4);
                v_messages_2170_ = lean_ctor_get(v___x_2164_, 6);
                v_infoState_2171_ = lean_ctor_get(v___x_2164_, 7);
                v_snapshotTasks_2172_ = lean_ctor_get(v___x_2164_, 8);
                v_isSharedCheck_2190_ = (!lean_is_exclusive(v___x_2164_)) as u8;
                if v_isSharedCheck_2190_ == 0 {
                    v_unused_2191_ = lean_ctor_get(v___x_2164_, 5);
                    lean_dec(v_unused_2191_);
                    v___x_2174_ = v___x_2164_;
                    v_isShared_2175_ = v_isSharedCheck_2190_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2172_);
                    lean_inc(v_infoState_2171_);
                    lean_inc(v_messages_2170_);
                    lean_inc(v_traceState_2169_);
                    lean_inc(v_auxDeclNGen_2168_);
                    lean_inc(v_ngen_2167_);
                    lean_inc(v_nextMacroScope_2166_);
                    lean_inc(v_env_2165_);
                    lean_dec(v___x_2164_);
                    v___x_2174_ = lean_box(0);
                    v_isShared_2175_ = v_isSharedCheck_2190_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2176_ = l_Lean_CodeAction_holeCodeActionExt;
                v_toEnvExtension_2177_ = lean_ctor_get(v___x_2176_, 0);
                v_asyncMode_2178_ = lean_ctor_get(v_toEnvExtension_2177_, 2);
                v___x_2179_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2179_, 0, v_decl_2138_);
                lean_ctor_set(v___x_2179_, 1, v_a_2160_);
                v___x_2180_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_2176_,
                    v_env_2165_,
                    v___x_2179_,
                    v_asyncMode_2178_,
                    v___x_2137_,
                );
                v___x_2181_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_);
                if v_isShared_2175_ == 0 {
                    lean_ctor_set(v___x_2174_, 5, v___x_2181_);
                    lean_ctor_set(v___x_2174_, 0, v___x_2180_);
                    v___x_2183_ = v___x_2174_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2180_);
                    lean_ctor_set(v_reuseFailAlloc_2189_, 1, v_nextMacroScope_2166_);
                    lean_ctor_set(v_reuseFailAlloc_2189_, 2, v_ngen_2167_);
                    lean_ctor_set(v_reuseFailAlloc_2189_, 3, v_auxDeclNGen_2168_);
                    lean_ctor_set(v_reuseFailAlloc_2189_, 4, v_traceState_2169_);
                    lean_ctor_set(v_reuseFailAlloc_2189_, 5, v___x_2181_);
                    lean_ctor_set(v_reuseFailAlloc_2189_, 6, v_messages_2170_);
                    lean_ctor_set(v_reuseFailAlloc_2189_, 7, v_infoState_2171_);
                    lean_ctor_set(v_reuseFailAlloc_2189_, 8, v_snapshotTasks_2172_);
                    v___x_2183_ = v_reuseFailAlloc_2189_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2184_ = lean_st_ref_set(v___y_2146_, v___x_2183_);
                v___x_2185_ = lean_box(0);
                if v_isShared_2163_ == 0 {
                    lean_ctor_set(v___x_2162_, 0, v___x_2185_);
                    v___x_2187_ = v___x_2162_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2185_);
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
                v___x_2198_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2198_, 0, v___x_2197_);
                v___x_2199_ = l_Lean_MessageData_ofFormat(v___x_2198_);
                lean_inc(v_ref_2157_);
                v___x_2200_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2200_, 0, v_ref_2157_);
                lean_ctor_set(v___x_2200_, 1, v___x_2199_);
                if v_isShared_2196_ == 0 {
                    lean_ctor_set(v___x_2195_, 0, v___x_2200_);
                    v___x_2202_ = v___x_2195_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2200_);
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
    mut v___x_2215_: *mut LeanObject,
    mut v___x_2216_: *mut LeanObject,
    mut v_decl_2217_: *mut LeanObject,
    mut v_stx_2218_: *mut LeanObject,
    mut v_kind_2219_: *mut LeanObject,
    mut v___y_2220_: *mut LeanObject,
    mut v___y_2221_: *mut LeanObject,
    mut v___y_2222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_2223_: u8 = 0;
    let mut v_res_2224_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_2223_ = (lean_unbox(v_kind_2219_) as u8);
    v_res_2224_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_(v___x_2215_, v___x_2216_, v_decl_2217_, v_stx_2218_, v_kind_boxed_2223_, v___y_2220_, v___y_2221_);
    lean_dec(v___y_2221_);
    lean_dec_ref(v___y_2220_);
    return v_res_2224_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    v___x_2226_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__0_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_;
    v___x_2227_ = l_Lean_stringToMessageData(v___x_2226_);
    return v___x_2227_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    v___x_2229_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_;
    v___x_2230_ = l_Lean_stringToMessageData(v___x_2229_);
    return v___x_2230_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_(
    mut v___x_2231_: *mut LeanObject,
    mut v_decl_2232_: *mut LeanObject,
    mut v___y_2233_: *mut LeanObject,
    mut v___y_2234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    v___x_2236_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_);
    v___x_2237_ = l_Lean_MessageData_ofName(v___x_2231_);
    v___x_2238_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2238_, 0, v___x_2236_);
    lean_ctor_set(v___x_2238_, 1, v___x_2237_);
    v___x_2239_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_);
    v___x_2240_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2240_, 0, v___x_2238_);
    lean_ctor_set(v___x_2240_, 1, v___x_2239_);
    v___x_2241_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0___redArg(v___x_2240_, v___y_2233_, v___y_2234_);
    return v___x_2241_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2____boxed(
    mut v___x_2242_: *mut LeanObject,
    mut v_decl_2243_: *mut LeanObject,
    mut v___y_2244_: *mut LeanObject,
    mut v___y_2245_: *mut LeanObject,
    mut v___y_2246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2247_: *mut LeanObject = core::ptr::null_mut();
    v_res_2247_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_(v___x_2242_, v_decl_2243_, v___y_2244_, v___y_2245_);
    lean_dec(v___y_2245_);
    lean_dec_ref(v___y_2244_);
    lean_dec(v_decl_2243_);
    return v_res_2247_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    v___x_2329_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__32_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_;
    v___x_2330_ = l_Lean_registerBuiltinAttribute(v___x_2329_);
    return v___x_2330_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2____boxed(
    mut v_a_2331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2332_: *mut LeanObject = core::ptr::null_mut();
    v_res_2332_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_();
    return v_res_2332_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0(
    mut v_00_u03b1_2333_: *mut LeanObject,
    mut v_msg_2334_: *mut LeanObject,
    mut v___y_2335_: *mut LeanObject,
    mut v___y_2336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    v___x_2338_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0___redArg(v_msg_2334_, v___y_2335_, v___y_2336_);
    return v___x_2338_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b1_2339_: *mut LeanObject,
    mut v_msg_2340_: *mut LeanObject,
    mut v___y_2341_: *mut LeanObject,
    mut v___y_2342_: *mut LeanObject,
    mut v___y_2343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2344_: *mut LeanObject = core::ptr::null_mut();
    v_res_2344_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0(v_00_u03b1_2339_, v_msg_2340_, v___y_2341_, v___y_2342_);
    lean_dec(v___y_2342_);
    lean_dec_ref(v___y_2341_);
    return v_res_2344_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1(
    mut v_00_u03b1_2345_: *mut LeanObject,
    mut v_name_2346_: *mut LeanObject,
    mut v_kind_2347_: u8,
    mut v___y_2348_: *mut LeanObject,
    mut v___y_2349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    v___x_2351_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg(v_name_2346_, v_kind_2347_, v___y_2348_, v___y_2349_);
    return v___x_2351_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___boxed(
    mut v_00_u03b1_2352_: *mut LeanObject,
    mut v_name_2353_: *mut LeanObject,
    mut v_kind_2354_: *mut LeanObject,
    mut v___y_2355_: *mut LeanObject,
    mut v___y_2356_: *mut LeanObject,
    mut v___y_2357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_2358_: u8 = 0;
    let mut v_res_2359_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_2358_ = (lean_unbox(v_kind_2354_) as u8);
    v_res_2359_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1(v_00_u03b1_2352_, v_name_2353_, v_kind_boxed_2358_, v___y_2355_, v___y_2356_);
    lean_dec(v___y_2356_);
    lean_dec_ref(v___y_2355_);
    return v_res_2359_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1(
    mut v_n_2365_: *mut LeanObject,
    mut v_env_2366_: *mut LeanObject,
    mut v_opts_2367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_n_2370_: *mut LeanObject,
    mut v_env_2371_: *mut LeanObject,
    mut v_opts_2372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2373_: *mut LeanObject = core::ptr::null_mut();
    v_res_2373_ =
        l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_mkCommandCodeAction_unsafe__1(
            v_n_2370_,
            v_env_2371_,
            v_opts_2372_,
        );
    lean_dec_ref(v_opts_2372_);
    return v_res_2373_;
}
pub unsafe fn l_Lean_CodeAction_mkCommandCodeAction(
    mut v_n_2374_: *mut LeanObject,
    mut v_a_2375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_env_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    v_env_2377_ = lean_ctor_get(v_a_2375_, 0);
    v_opts_2378_ = lean_ctor_get(v_a_2375_, 1);
    lean_inc_ref(v_env_2377_);
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
    mut v_n_2381_: *mut LeanObject,
    mut v_a_2382_: *mut LeanObject,
    mut v_a_2383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2384_: *mut LeanObject = core::ptr::null_mut();
    v_res_2384_ = l_Lean_CodeAction_mkCommandCodeAction(v_n_2381_, v_a_2382_);
    lean_dec_ref(v_a_2382_);
    return v_res_2384_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_CodeAction_CommandCodeActions_insert_spec__0___redArg(
    mut v_t_2399_: *mut LeanObject,
    mut v_k_2400_: *mut LeanObject,
    mut v_fallback_2401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_2399_) == 0 {
                    v_k_2402_ = lean_ctor_get(v_t_2399_, 1);
                    v_v_2403_ = lean_ctor_get(v_t_2399_, 2);
                    v_l_2404_ = lean_ctor_get(v_t_2399_, 3);
                    v_r_2405_ = lean_ctor_get(v_t_2399_, 4);
                    v___x_2406_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2400_, v_k_2402_);
                    match v___x_2406_ {
                        0 => {
                            v_t_2399_ = v_l_2404_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_inc(v_v_2403_);
                            return v_v_2403_;
                        }
                        _ => {
                            v_t_2399_ = v_r_2405_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_fallback_2401_);
                    return v_fallback_2401_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_CodeAction_CommandCodeActions_insert_spec__0___redArg___boxed(
    mut v_t_2409_: *mut LeanObject,
    mut v_k_2410_: *mut LeanObject,
    mut v_fallback_2411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2412_: *mut LeanObject = core::ptr::null_mut();
    v_res_2412_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_CodeAction_CommandCodeActions_insert_spec__0___redArg(v_t_2409_, v_k_2410_, v_fallback_2411_);
    lean_dec(v_fallback_2411_);
    lean_dec(v_k_2410_);
    lean_dec(v_t_2409_);
    return v_res_2412_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_CommandCodeActions_insert_spec__1(
    mut v_action_2415_: *mut LeanObject,
    mut v_as_2416_: *mut LeanObject,
    mut v_i_2417_: usize,
    mut v_stop_2418_: usize,
    mut v_b_2419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2420_: u8 = 0;
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_action_2415_);
                    v___x_2424_ = lean_array_push(v___x_2423_, v_action_2415_);
                    lean_inc(v___x_2421_);
                    v___x_2425_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_2421_, v___x_2424_, v_b_2419_);
                    v___x_2426_ = 1usize;
                    v___x_2427_ = lean_usize_add(v_i_2417_, v___x_2426_);
                    v_i_2417_ = v___x_2427_;
                    v_b_2419_ = v___x_2425_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_action_2415_);
                    return v_b_2419_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_CommandCodeActions_insert_spec__1___boxed(
    mut v_action_2429_: *mut LeanObject,
    mut v_as_2430_: *mut LeanObject,
    mut v_i_2431_: *mut LeanObject,
    mut v_stop_2432_: *mut LeanObject,
    mut v_b_2433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2434_: usize = 0;
    let mut v_stop_boxed_2435_: usize = 0;
    let mut v_res_2436_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2434_ = lean_unbox_usize(v_i_2431_);
    lean_dec(v_i_2431_);
    v_stop_boxed_2435_ = lean_unbox_usize(v_stop_2432_);
    lean_dec(v_stop_2432_);
    v_res_2436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_CommandCodeActions_insert_spec__1(v_action_2429_, v_as_2430_, v_i_boxed_2434_, v_stop_boxed_2435_, v_b_2433_);
    lean_dec_ref(v_as_2430_);
    return v_res_2436_;
}
pub unsafe fn l_Lean_CodeAction_CommandCodeActions_insert(
    mut v_self_2437_: *mut LeanObject,
    mut v_tacticKinds_2438_: *mut LeanObject,
    mut v_action_2439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: u8 = 0;
    let mut v_onAnyCmd_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_onCmd_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: u8 = 0;
    let mut v___x_2446_: u8 = 0;
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2449_: u8 = 0;
    let mut v___x_2450_: usize = 0;
    let mut v___x_2451_: usize = 0;
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2456_: u8 = 0;
    let mut v_unused_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2461_: u8 = 0;
    let mut v___x_2462_: usize = 0;
    let mut v___x_2463_: usize = 0;
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2468_: u8 = 0;
    let mut v_unused_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_onAnyCmd_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_onCmd_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2475_: u8 = 0;
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2480_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2440_ = lean_array_get_size(v_tacticKinds_2438_);
                v___x_2441_ = lean_unsigned_to_nat(0);
                v___x_2442_ = lean_nat_dec_eq(v___x_2440_, v___x_2441_);
                if v___x_2442_ == 0 {
                    v_onAnyCmd_2443_ = lean_ctor_get(v_self_2437_, 0);
                    v_onCmd_2444_ = lean_ctor_get(v_self_2437_, 1);
                    v___x_2445_ = lean_nat_dec_lt(v___x_2441_, v___x_2440_);
                    if v___x_2445_ == 0 {
                        lean_dec_ref(v_action_2439_);
                        return v_self_2437_;
                    } else {
                        v___x_2446_ = lean_nat_dec_le(v___x_2440_, v___x_2440_);
                        if v___x_2446_ == 0 {
                            if v___x_2445_ == 0 {
                                lean_dec_ref(v_action_2439_);
                                return v_self_2437_;
                            } else {
                                lean_inc(v_onCmd_2444_);
                                lean_inc_ref(v_onAnyCmd_2443_);
                                v_isSharedCheck_2456_ = (!lean_is_exclusive(v_self_2437_)) as u8;
                                if v_isSharedCheck_2456_ == 0 {
                                    v_unused_2457_ = lean_ctor_get(v_self_2437_, 1);
                                    lean_dec(v_unused_2457_);
                                    v_unused_2458_ = lean_ctor_get(v_self_2437_, 0);
                                    lean_dec(v_unused_2458_);
                                    v___x_2448_ = v_self_2437_;
                                    v_isShared_2449_ = v_isSharedCheck_2456_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v_self_2437_);
                                    v___x_2448_ = lean_box(0);
                                    v_isShared_2449_ = v_isSharedCheck_2456_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_inc(v_onCmd_2444_);
                            lean_inc_ref(v_onAnyCmd_2443_);
                            v_isSharedCheck_2468_ = (!lean_is_exclusive(v_self_2437_)) as u8;
                            if v_isSharedCheck_2468_ == 0 {
                                v_unused_2469_ = lean_ctor_get(v_self_2437_, 1);
                                lean_dec(v_unused_2469_);
                                v_unused_2470_ = lean_ctor_get(v_self_2437_, 0);
                                lean_dec(v_unused_2470_);
                                v___x_2460_ = v_self_2437_;
                                v_isShared_2461_ = v_isSharedCheck_2468_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v_self_2437_);
                                v___x_2460_ = lean_box(0);
                                v_isShared_2461_ = v_isSharedCheck_2468_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v_onAnyCmd_2471_ = lean_ctor_get(v_self_2437_, 0);
                    v_onCmd_2472_ = lean_ctor_get(v_self_2437_, 1);
                    v_isSharedCheck_2480_ = (!lean_is_exclusive(v_self_2437_)) as u8;
                    if v_isSharedCheck_2480_ == 0 {
                        v___x_2474_ = v_self_2437_;
                        v_isShared_2475_ = v_isSharedCheck_2480_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_onCmd_2472_);
                        lean_inc(v_onAnyCmd_2471_);
                        lean_dec(v_self_2437_);
                        v___x_2474_ = lean_box(0);
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
                    lean_ctor_set(v___x_2448_, 1, v___x_2452_);
                    v___x_2454_ = v___x_2448_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_onAnyCmd_2443_);
                    lean_ctor_set(v_reuseFailAlloc_2455_, 1, v___x_2452_);
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
                    lean_ctor_set(v___x_2460_, 1, v___x_2464_);
                    v___x_2466_ = v___x_2460_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_onAnyCmd_2443_);
                    lean_ctor_set(v_reuseFailAlloc_2467_, 1, v___x_2464_);
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
                    lean_ctor_set(v___x_2474_, 0, v___x_2476_);
                    v___x_2478_ = v___x_2474_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2476_);
                    lean_ctor_set(v_reuseFailAlloc_2479_, 1, v_onCmd_2472_);
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
    mut v_self_2481_: *mut LeanObject,
    mut v_tacticKinds_2482_: *mut LeanObject,
    mut v_action_2483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2484_: *mut LeanObject = core::ptr::null_mut();
    v_res_2484_ = l_Lean_CodeAction_CommandCodeActions_insert(
        v_self_2481_,
        v_tacticKinds_2482_,
        v_action_2483_,
    );
    lean_dec_ref(v_tacticKinds_2482_);
    return v_res_2484_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_CodeAction_CommandCodeActions_insert_spec__0(
    mut v_00_u03b4_2485_: *mut LeanObject,
    mut v_t_2486_: *mut LeanObject,
    mut v_k_2487_: *mut LeanObject,
    mut v_fallback_2488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    v___x_2489_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_CodeAction_CommandCodeActions_insert_spec__0___redArg(v_t_2486_, v_k_2487_, v_fallback_2488_);
    return v___x_2489_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_CodeAction_CommandCodeActions_insert_spec__0___boxed(
    mut v_00_u03b4_2490_: *mut LeanObject,
    mut v_t_2491_: *mut LeanObject,
    mut v_k_2492_: *mut LeanObject,
    mut v_fallback_2493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2494_: *mut LeanObject = core::ptr::null_mut();
    v_res_2494_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_CodeAction_CommandCodeActions_insert_spec__0(v_00_u03b4_2490_, v_t_2491_, v_k_2492_, v_fallback_2493_);
    lean_dec(v_fallback_2493_);
    lean_dec(v_k_2492_);
    lean_dec(v_t_2491_);
    return v_res_2494_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_262607364____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    v___x_2496_ = l_Lean_CodeAction_instInhabitedCommandCodeActions_default___closed__1;
    v___x_2497_ = lean_st_mk_ref(v___x_2496_);
    v___x_2498_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2498_, 0, v___x_2497_);
    return v___x_2498_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_262607364____hygCtx___hyg_2____boxed(
    mut v_a_2499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2500_: *mut LeanObject = core::ptr::null_mut();
    v_res_2500_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_262607364____hygCtx___hyg_2_();
    return v_res_2500_;
}
pub unsafe fn l_Lean_CodeAction_insertBuiltin(
    mut v_args_2501_: *mut LeanObject,
    mut v_proc_2502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    v___x_2504_ = l_Lean_CodeAction_builtinCmdCodeActions;
    v___x_2505_ = lean_st_ref_take(v___x_2504_);
    v___x_2506_ =
        l_Lean_CodeAction_CommandCodeActions_insert(v___x_2505_, v_args_2501_, v_proc_2502_);
    v___x_2507_ = lean_st_ref_set(v___x_2504_, v___x_2506_);
    v___x_2508_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2508_, 0, v___x_2507_);
    return v___x_2508_;
}
pub unsafe fn l_Lean_CodeAction_insertBuiltin___boxed(
    mut v_args_2509_: *mut LeanObject,
    mut v_proc_2510_: *mut LeanObject,
    mut v_a_2511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2512_: *mut LeanObject = core::ptr::null_mut();
    v_res_2512_ = l_Lean_CodeAction_insertBuiltin(v_args_2509_, v_proc_2510_);
    lean_dec_ref(v_args_2509_);
    return v_res_2512_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(
    mut v_x_2513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2514_: *mut LeanObject = core::ptr::null_mut();
    v_fst_2514_ = lean_ctor_get(v_x_2513_, 0);
    lean_inc(v_fst_2514_);
    return v_fst_2514_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed(
    mut v_x_2515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2516_: *mut LeanObject = core::ptr::null_mut();
    v_res_2516_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(v_x_2515_);
    lean_dec_ref(v_x_2515_);
    return v_res_2516_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(
    mut v_x_2517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    v___x_2518_ = lean_box(0);
    return v___x_2518_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed(
    mut v_x_2519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2520_: *mut LeanObject = core::ptr::null_mut();
    v_res_2520_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(v_x_2519_);
    lean_dec_ref(v_x_2519_);
    return v_res_2520_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__2_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(
    mut v_x_2521_: *mut LeanObject,
    mut v_s_2522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    v_fst_2523_ = lean_ctor_get(v_s_2522_, 0);
    lean_inc_n(v_fst_2523_, 3);
    v___x_2524_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2524_, 0, v_fst_2523_);
    lean_ctor_set(v___x_2524_, 1, v_fst_2523_);
    lean_ctor_set(v___x_2524_, 2, v_fst_2523_);
    return v___x_2524_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__2_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed(
    mut v_x_2525_: *mut LeanObject,
    mut v_s_2526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2527_: *mut LeanObject = core::ptr::null_mut();
    v_res_2527_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__2_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(v_x_2525_, v_s_2526_);
    lean_dec_ref(v_s_2526_);
    lean_dec_ref(v_x_2525_);
    return v_res_2527_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__3_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(
    mut v_x_2528_: *mut LeanObject,
    mut v_x_2529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2536_: u8 = 0;
    let mut v_cmdKinds_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2543_: u8 = 0;
    let mut v_unused_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2530_ = lean_ctor_get(v_x_2529_, 0);
                lean_inc(v_fst_2530_);
                v_fst_2531_ = lean_ctor_get(v_x_2528_, 0);
                lean_inc(v_fst_2531_);
                v_snd_2532_ = lean_ctor_get(v_x_2528_, 1);
                lean_inc(v_snd_2532_);
                lean_dec_ref(v_x_2528_);
                v_snd_2533_ = lean_ctor_get(v_x_2529_, 1);
                v_isSharedCheck_2543_ = (!lean_is_exclusive(v_x_2529_)) as u8;
                if v_isSharedCheck_2543_ == 0 {
                    v_unused_2544_ = lean_ctor_get(v_x_2529_, 0);
                    lean_dec(v_unused_2544_);
                    v___x_2535_ = v_x_2529_;
                    v_isShared_2536_ = v_isSharedCheck_2543_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_2533_);
                    lean_dec(v_x_2529_);
                    v___x_2535_ = lean_box(0);
                    v_isShared_2536_ = v_isSharedCheck_2543_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_cmdKinds_2537_ = lean_ctor_get(v_fst_2530_, 1);
                lean_inc_ref(v_cmdKinds_2537_);
                v___x_2538_ = lean_array_push(v_fst_2531_, v_fst_2530_);
                v___x_2539_ = l_Lean_CodeAction_CommandCodeActions_insert(
                    v_snd_2532_,
                    v_cmdKinds_2537_,
                    v_snd_2533_,
                );
                lean_dec_ref(v_cmdKinds_2537_);
                if v_isShared_2536_ == 0 {
                    lean_ctor_set(v___x_2535_, 1, v___x_2539_);
                    lean_ctor_set(v___x_2535_, 0, v___x_2538_);
                    v___x_2541_ = v___x_2535_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2542_, 0, v___x_2538_);
                    lean_ctor_set(v_reuseFailAlloc_2542_, 1, v___x_2539_);
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
    mut v___x_2547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    v___x_2549_ = lean_st_ref_get(v___x_2547_);
    v___x_2550_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__4___closed__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_;
    v___x_2551_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2551_, 0, v___x_2550_);
    lean_ctor_set(v___x_2551_, 1, v___x_2549_);
    v___x_2552_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2552_, 0, v___x_2551_);
    return v___x_2552_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__4_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed(
    mut v___x_2553_: *mut LeanObject,
    mut v___y_2554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2555_: *mut LeanObject = core::ptr::null_mut();
    v_res_2555_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__4_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(v___x_2553_);
    lean_dec(v___x_2553_);
    return v_res_2555_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__spec__0(
    mut v_as_2556_: *mut LeanObject,
    mut v_i_2557_: usize,
    mut v_stop_2558_: usize,
    mut v_b_2559_: *mut LeanObject,
    mut v___y_2560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2562_: u8 = 0;
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cmdKinds_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: usize = 0;
    let mut v___x_2570_: usize = 0;
    let mut v_a_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2575_: u8 = 0;
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2579_: u8 = 0;
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2562_ = lean_usize_dec_eq(v_i_2557_, v_stop_2558_);
                if v___x_2562_ == 0 {
                    v___x_2563_ = lean_array_uget_borrowed(v_as_2556_, v_i_2557_);
                    v_declName_2564_ = lean_ctor_get(v___x_2563_, 0);
                    v_cmdKinds_2565_ = lean_ctor_get(v___x_2563_, 1);
                    lean_inc(v_declName_2564_);
                    v___x_2566_ =
                        l_Lean_CodeAction_mkCommandCodeAction(v_declName_2564_, v___y_2560_);
                    if lean_obj_tag(v___x_2566_) == 0 {
                        v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
                        lean_inc(v_a_2567_);
                        lean_dec_ref_known(v___x_2566_, 1);
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
                        lean_dec_ref(v_b_2559_);
                        v_a_2572_ = lean_ctor_get(v___x_2566_, 0);
                        v_isSharedCheck_2579_ = (!lean_is_exclusive(v___x_2566_)) as u8;
                        if v_isSharedCheck_2579_ == 0 {
                            v___x_2574_ = v___x_2566_;
                            v_isShared_2575_ = v_isSharedCheck_2579_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2572_);
                            lean_dec(v___x_2566_);
                            v___x_2574_ = lean_box(0);
                            v_isShared_2575_ = v_isSharedCheck_2579_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_2580_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2580_, 0, v_b_2559_);
                    return v___x_2580_;
                }
            }
            1 => {
                if v_isShared_2575_ == 0 {
                    v___x_2577_ = v___x_2574_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
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
    mut v_as_2581_: *mut LeanObject,
    mut v_i_2582_: *mut LeanObject,
    mut v_stop_2583_: *mut LeanObject,
    mut v_b_2584_: *mut LeanObject,
    mut v___y_2585_: *mut LeanObject,
    mut v___y_2586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2587_: usize = 0;
    let mut v_stop_boxed_2588_: usize = 0;
    let mut v_res_2589_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2587_ = lean_unbox_usize(v_i_2582_);
    lean_dec(v_i_2582_);
    v_stop_boxed_2588_ = lean_unbox_usize(v_stop_2583_);
    lean_dec(v_stop_2583_);
    v_res_2589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__spec__0(v_as_2581_, v_i_boxed_2587_, v_stop_boxed_2588_, v_b_2584_, v___y_2585_);
    lean_dec_ref(v___y_2585_);
    lean_dec_ref(v_as_2581_);
    return v_res_2589_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__spec__1(
    mut v_as_2590_: *mut LeanObject,
    mut v_i_2591_: usize,
    mut v_stop_2592_: usize,
    mut v_b_2593_: *mut LeanObject,
    mut v___y_2594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: usize = 0;
    let mut v___x_2599_: usize = 0;
    let mut v___y_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: u8 = 0;
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: u8 = 0;
    let mut v___x_2609_: u8 = 0;
    let mut v___x_2610_: usize = 0;
    let mut v___x_2611_: usize = 0;
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: usize = 0;
    let mut v___x_2614_: usize = 0;
    let mut v___x_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2604_ = lean_usize_dec_eq(v_i_2591_, v_stop_2592_);
                if v___x_2604_ == 0 {
                    v___x_2605_ = lean_array_uget_borrowed(v_as_2590_, v_i_2591_);
                    v___x_2606_ = lean_unsigned_to_nat(0);
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
                    v___x_2616_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2616_, 0, v_b_2593_);
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
                if lean_obj_tag(v___y_2602_) == 0 {
                    v_a_2603_ = lean_ctor_get(v___y_2602_, 0);
                    lean_inc(v_a_2603_);
                    lean_dec_ref_known(v___y_2602_, 1);
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
    mut v_as_2617_: *mut LeanObject,
    mut v_i_2618_: *mut LeanObject,
    mut v_stop_2619_: *mut LeanObject,
    mut v_b_2620_: *mut LeanObject,
    mut v___y_2621_: *mut LeanObject,
    mut v___y_2622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2623_: usize = 0;
    let mut v_stop_boxed_2624_: usize = 0;
    let mut v_res_2625_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2623_ = lean_unbox_usize(v_i_2618_);
    lean_dec(v_i_2618_);
    v_stop_boxed_2624_ = lean_unbox_usize(v_stop_2619_);
    lean_dec(v_stop_2619_);
    v_res_2625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__spec__1(v_as_2617_, v_i_boxed_2623_, v_stop_boxed_2624_, v_b_2620_, v___y_2621_);
    lean_dec_ref(v___y_2621_);
    lean_dec_ref(v_as_2617_);
    return v_res_2625_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(
    mut v___x_2626_: *mut LeanObject,
    mut v_as_2627_: *mut LeanObject,
    mut v___y_2628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2643_: u8 = 0;
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2647_: u8 = 0;
    let mut v___x_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: u8 = 0;
    let mut v___x_2650_: u8 = 0;
    let mut v___x_2651_: usize = 0;
    let mut v___x_2652_: usize = 0;
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: usize = 0;
    let mut v___x_2655_: usize = 0;
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2630_ = lean_st_ref_get(v___x_2626_);
                v___x_2631_ = lean_unsigned_to_nat(0);
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
                v___x_2635_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2635_, 0, v___x_2634_);
                lean_ctor_set(v___x_2635_, 1, v_a_2633_);
                v___x_2636_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2636_, 0, v___x_2635_);
                return v___x_2636_;
            }
            2 => {
                if lean_obj_tag(v___y_2638_) == 0 {
                    v_a_2639_ = lean_ctor_get(v___y_2638_, 0);
                    lean_inc(v_a_2639_);
                    lean_dec_ref_known(v___y_2638_, 1);
                    v_a_2633_ = v_a_2639_;
                    state = 1;
                    continue;
                } else {
                    v_a_2640_ = lean_ctor_get(v___y_2638_, 0);
                    v_isSharedCheck_2647_ = (!lean_is_exclusive(v___y_2638_)) as u8;
                    if v_isSharedCheck_2647_ == 0 {
                        v___x_2642_ = v___y_2638_;
                        v_isShared_2643_ = v_isSharedCheck_2647_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2640_);
                        lean_dec(v___y_2638_);
                        v___x_2642_ = lean_box(0);
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
                    v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2640_);
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
    mut v___x_2657_: *mut LeanObject,
    mut v_as_2658_: *mut LeanObject,
    mut v___y_2659_: *mut LeanObject,
    mut v___y_2660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2661_: *mut LeanObject = core::ptr::null_mut();
    v_res_2661_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_(v___x_2657_, v_as_2658_, v___y_2659_);
    lean_dec_ref(v___y_2659_);
    lean_dec_ref(v_as_2658_);
    lean_dec(v___x_2657_);
    return v_res_2661_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2672_: *mut LeanObject = core::ptr::null_mut();
    v___x_2671_ = l_Lean_CodeAction_builtinCmdCodeActions;
    v___f_2672_ = lean_alloc_closure(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__4_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_2672_, 0, v___x_2671_);
    return v___f_2672_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2674_: *mut LeanObject = core::ptr::null_mut();
    v___x_2673_ = l_Lean_CodeAction_builtinCmdCodeActions;
    v___f_2674_ = lean_alloc_closure(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 4, 1);
    lean_closure_set(v___f_2674_, 0, v___x_2673_);
    return v___f_2674_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    v___x_2675_ = lean_box(0);
    v___x_2676_ = lean_box(2);
    v___f_2677_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__1_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_;
    v___f_2678_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__2_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_;
    v___f_2679_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__3_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_;
    v___f_2680_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__7_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_);
    v___f_2681_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__6_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_);
    v___x_2682_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__5_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_;
    v___x_2683_ = lean_alloc_ctor(0, 8, (0) as u32);
    lean_ctor_set(v___x_2683_, 0, v___x_2682_);
    lean_ctor_set(v___x_2683_, 1, v___f_2681_);
    lean_ctor_set(v___x_2683_, 2, v___f_2680_);
    lean_ctor_set(v___x_2683_, 3, v___f_2679_);
    lean_ctor_set(v___x_2683_, 4, v___f_2678_);
    lean_ctor_set(v___x_2683_, 5, v___f_2677_);
    lean_ctor_set(v___x_2683_, 6, v___x_2676_);
    lean_ctor_set(v___x_2683_, 7, v___x_2675_);
    return v___x_2683_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
    v___f_2684_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__0_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_;
    v___x_2685_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__8_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_);
    v___x_2686_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2686_, 0, v___x_2685_);
    lean_ctor_set(v___x_2686_, 1, v___f_2684_);
    return v___x_2686_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    v___x_2688_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2__once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__9_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_);
    v___x_2689_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2688_);
    return v___x_2689_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2____boxed(
    mut v_a_2690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2691_: *mut LeanObject = core::ptr::null_mut();
    v_res_2691_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_();
    return v_res_2691_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___closed__0()
-> f64 {
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: f64 = 0.0;
    v___x_2692_ = lean_unsigned_to_nat(0);
    v___x_2693_ = lean_float_of_nat(v___x_2692_);
    return v___x_2693_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3(
    mut v_cls_2697_: *mut LeanObject,
    mut v_msg_2698_: *mut LeanObject,
    mut v___y_2699_: *mut LeanObject,
    mut v___y_2700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2707_: u8 = 0;
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2720_: u8 = 0;
    let mut v_tid_2721_: u64 = 0;
    let mut v_traces_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2725_: u8 = 0;
    let mut v___x_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: f64 = 0.0;
    let mut v___x_2728_: u8 = 0;
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2746_: u8 = 0;
    let mut v_isSharedCheck_2747_: u8 = 0;
    let mut v_isSharedCheck_2748_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2702_ = lean_ctor_get(v___y_2699_, 5);
                v___x_2703_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0(v_msg_2698_, v___y_2699_, v___y_2700_);
                v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
                v_isSharedCheck_2748_ = (!lean_is_exclusive(v___x_2703_)) as u8;
                if v_isSharedCheck_2748_ == 0 {
                    v___x_2706_ = v___x_2703_;
                    v_isShared_2707_ = v_isSharedCheck_2748_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2704_);
                    lean_dec(v___x_2703_);
                    v___x_2706_ = lean_box(0);
                    v_isShared_2707_ = v_isSharedCheck_2748_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2708_ = lean_st_ref_take(v___y_2700_);
                v_traceState_2709_ = lean_ctor_get(v___x_2708_, 4);
                v_env_2710_ = lean_ctor_get(v___x_2708_, 0);
                v_nextMacroScope_2711_ = lean_ctor_get(v___x_2708_, 1);
                v_ngen_2712_ = lean_ctor_get(v___x_2708_, 2);
                v_auxDeclNGen_2713_ = lean_ctor_get(v___x_2708_, 3);
                v_cache_2714_ = lean_ctor_get(v___x_2708_, 5);
                v_messages_2715_ = lean_ctor_get(v___x_2708_, 6);
                v_infoState_2716_ = lean_ctor_get(v___x_2708_, 7);
                v_snapshotTasks_2717_ = lean_ctor_get(v___x_2708_, 8);
                v_isSharedCheck_2747_ = (!lean_is_exclusive(v___x_2708_)) as u8;
                if v_isSharedCheck_2747_ == 0 {
                    v___x_2719_ = v___x_2708_;
                    v_isShared_2720_ = v_isSharedCheck_2747_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2717_);
                    lean_inc(v_infoState_2716_);
                    lean_inc(v_messages_2715_);
                    lean_inc(v_cache_2714_);
                    lean_inc(v_traceState_2709_);
                    lean_inc(v_auxDeclNGen_2713_);
                    lean_inc(v_ngen_2712_);
                    lean_inc(v_nextMacroScope_2711_);
                    lean_inc(v_env_2710_);
                    lean_dec(v___x_2708_);
                    v___x_2719_ = lean_box(0);
                    v_isShared_2720_ = v_isSharedCheck_2747_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2721_ = lean_ctor_get_uint64(
                    v_traceState_2709_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_2722_ = lean_ctor_get(v_traceState_2709_, 0);
                v_isSharedCheck_2746_ = (!lean_is_exclusive(v_traceState_2709_)) as u8;
                if v_isSharedCheck_2746_ == 0 {
                    v___x_2724_ = v_traceState_2709_;
                    v_isShared_2725_ = v_isSharedCheck_2746_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_2722_);
                    lean_dec(v_traceState_2709_);
                    v___x_2724_ = lean_box(0);
                    v_isShared_2725_ = v_isSharedCheck_2746_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2726_ = lean_box(0);
                v___x_2727_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___closed__0);
                v___x_2728_ = 0;
                v___x_2729_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___closed__1;
                v___x_2730_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_2730_, 0, v_cls_2697_);
                lean_ctor_set(v___x_2730_, 1, v___x_2726_);
                lean_ctor_set(v___x_2730_, 2, v___x_2729_);
                lean_ctor_set_float(
                    v___x_2730_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_2727_,
                );
                lean_ctor_set_float(
                    v___x_2730_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_2727_,
                );
                lean_ctor_set_uint8(
                    v___x_2730_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_2728_,
                );
                v___x_2731_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___closed__2;
                v___x_2732_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_2732_, 0, v___x_2730_);
                lean_ctor_set(v___x_2732_, 1, v_a_2704_);
                lean_ctor_set(v___x_2732_, 2, v___x_2731_);
                lean_inc(v_ref_2702_);
                v___x_2733_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2733_, 0, v_ref_2702_);
                lean_ctor_set(v___x_2733_, 1, v___x_2732_);
                v___x_2734_ = l_Lean_PersistentArray_push___redArg(v_traces_2722_, v___x_2733_);
                if v_isShared_2725_ == 0 {
                    lean_ctor_set(v___x_2724_, 0, v___x_2734_);
                    v___x_2736_ = v___x_2724_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2745_, 0, v___x_2734_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_2745_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_2721_,
                    );
                    v___x_2736_ = v_reuseFailAlloc_2745_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2720_ == 0 {
                    lean_ctor_set(v___x_2719_, 4, v___x_2736_);
                    v___x_2738_ = v___x_2719_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_env_2710_);
                    lean_ctor_set(v_reuseFailAlloc_2744_, 1, v_nextMacroScope_2711_);
                    lean_ctor_set(v_reuseFailAlloc_2744_, 2, v_ngen_2712_);
                    lean_ctor_set(v_reuseFailAlloc_2744_, 3, v_auxDeclNGen_2713_);
                    lean_ctor_set(v_reuseFailAlloc_2744_, 4, v___x_2736_);
                    lean_ctor_set(v_reuseFailAlloc_2744_, 5, v_cache_2714_);
                    lean_ctor_set(v_reuseFailAlloc_2744_, 6, v_messages_2715_);
                    lean_ctor_set(v_reuseFailAlloc_2744_, 7, v_infoState_2716_);
                    lean_ctor_set(v_reuseFailAlloc_2744_, 8, v_snapshotTasks_2717_);
                    v___x_2738_ = v_reuseFailAlloc_2744_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2739_ = lean_st_ref_set(v___y_2700_, v___x_2738_);
                v___x_2740_ = lean_box(0);
                if v_isShared_2707_ == 0 {
                    lean_ctor_set(v___x_2706_, 0, v___x_2740_);
                    v___x_2742_ = v___x_2706_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___x_2740_);
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
    mut v_cls_2749_: *mut LeanObject,
    mut v_msg_2750_: *mut LeanObject,
    mut v___y_2751_: *mut LeanObject,
    mut v___y_2752_: *mut LeanObject,
    mut v___y_2753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2754_: *mut LeanObject = core::ptr::null_mut();
    v_res_2754_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3(v_cls_2749_, v_msg_2750_, v___y_2751_, v___y_2752_);
    lean_dec(v___y_2752_);
    lean_dec_ref(v___y_2751_);
    return v_res_2754_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4_spec__7___redArg(
    mut v_keys_2755_: *mut LeanObject,
    mut v_i_2756_: *mut LeanObject,
    mut v_k_2757_: *mut LeanObject,
) -> u8 {
    let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: u8 = 0;
    let mut v_k_x27_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: u8 = 0;
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2758_ = lean_array_get_size(v_keys_2755_);
                v___x_2759_ = lean_nat_dec_lt(v_i_2756_, v___x_2758_);
                if v___x_2759_ == 0 {
                    lean_dec(v_i_2756_);
                    return v___x_2759_;
                } else {
                    v_k_x27_2760_ = lean_array_fget_borrowed(v_keys_2755_, v_i_2756_);
                    v___x_2761_ = l_Lean_instBEqExtraModUse_beq(v_k_2757_, v_k_x27_2760_);
                    if v___x_2761_ == 0 {
                        v___x_2762_ = lean_unsigned_to_nat(1);
                        v___x_2763_ = lean_nat_add(v_i_2756_, v___x_2762_);
                        lean_dec(v_i_2756_);
                        v_i_2756_ = v___x_2763_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_2756_);
                        return v___x_2761_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4_spec__7___redArg___boxed(
    mut v_keys_2765_: *mut LeanObject,
    mut v_i_2766_: *mut LeanObject,
    mut v_k_2767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2768_: u8 = 0;
    let mut v_r_2769_: *mut LeanObject = core::ptr::null_mut();
    v_res_2768_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4_spec__7___redArg(v_keys_2765_, v_i_2766_, v_k_2767_);
    lean_dec_ref(v_k_2767_);
    lean_dec_ref(v_keys_2765_);
    v_r_2769_ = lean_box((v_res_2768_) as usize);
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
    v___x_2774_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__0);
    v___x_2775_ = lean_usize_sub(v___x_2774_, v___x_2773_);
    return v___x_2775_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg(
    mut v_x_2776_: *mut LeanObject,
    mut v_x_2777_: usize,
    mut v_x_2778_: *mut LeanObject,
) -> u8 {
    let mut v_es_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: usize = 0;
    let mut v___x_2782_: usize = 0;
    let mut v___x_2783_: usize = 0;
    let mut v_j_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: u8 = 0;
    let mut v_node_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: usize = 0;
    let mut v___x_2791_: u8 = 0;
    let mut v_ks_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2776_) == 0 {
                    v_es_2779_ = lean_ctor_get(v_x_2776_, 0);
                    v___x_2780_ = lean_box(2);
                    v___x_2781_ = 5usize;
                    v___x_2782_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___closed__1);
                    v___x_2783_ = lean_usize_land(v_x_2777_, v___x_2782_);
                    v_j_2784_ = lean_usize_to_nat(v___x_2783_);
                    v___x_2785_ = lean_array_get_borrowed(v___x_2780_, v_es_2779_, v_j_2784_);
                    lean_dec(v_j_2784_);
                    match lean_obj_tag(v___x_2785_) {
                        0 => {
                            v_key_2786_ = lean_ctor_get(v___x_2785_, 0);
                            v___x_2787_ = l_Lean_instBEqExtraModUse_beq(v_x_2778_, v_key_2786_);
                            return v___x_2787_;
                        }
                        1 => {
                            v_node_2788_ = lean_ctor_get(v___x_2785_, 0);
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
                    v_ks_2792_ = lean_ctor_get(v_x_2776_, 0);
                    v___x_2793_ = lean_unsigned_to_nat(0);
                    v___x_2794_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4_spec__7___redArg(v_ks_2792_, v___x_2793_, v_x_2778_);
                    return v___x_2794_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_x_2795_: *mut LeanObject,
    mut v_x_2796_: *mut LeanObject,
    mut v_x_2797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_6256__boxed_2798_: usize = 0;
    let mut v_res_2799_: u8 = 0;
    let mut v_r_2800_: *mut LeanObject = core::ptr::null_mut();
    v_x_6256__boxed_2798_ = lean_unbox_usize(v_x_2796_);
    lean_dec(v_x_2796_);
    v_res_2799_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg(v_x_2795_, v_x_6256__boxed_2798_, v_x_2797_);
    lean_dec_ref(v_x_2797_);
    lean_dec_ref(v_x_2795_);
    v_r_2800_ = lean_box((v_res_2799_) as usize);
    return v_r_2800_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(
    mut v_x_2801_: *mut LeanObject,
    mut v_x_2802_: *mut LeanObject,
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
    mut v_x_2806_: *mut LeanObject,
    mut v_x_2807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2808_: u8 = 0;
    let mut v_r_2809_: *mut LeanObject = core::ptr::null_mut();
    v_res_2808_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v_x_2806_, v_x_2807_);
    lean_dec_ref(v_x_2807_);
    lean_dec_ref(v_x_2806_);
    v_r_2809_ = lean_box((v_res_2808_) as usize);
    return v_r_2809_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__2()
-> *mut LeanObject {
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    v___x_2812_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__1;
    v___x_2813_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__0;
    v___x_2814_ =
        l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2813_, v___x_2812_);
    return v___x_2814_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__6()
-> *mut LeanObject {
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    v___x_2819_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__5;
    v___x_2820_ = l_Lean_stringToMessageData(v___x_2819_);
    return v___x_2820_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__8()
-> *mut LeanObject {
    let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    v___x_2822_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__7;
    v___x_2823_ = l_Lean_stringToMessageData(v___x_2822_);
    return v___x_2823_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__9()
-> *mut LeanObject {
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
    v___x_2824_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3___closed__1;
    v___x_2825_ = l_Lean_stringToMessageData(v___x_2824_);
    return v___x_2825_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__12()
-> *mut LeanObject {
    let mut v_cls_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    v_cls_2829_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__4;
    v___x_2830_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__11;
    v___x_2831_ = l_Lean_Name_append(v___x_2830_, v_cls_2829_);
    return v___x_2831_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__14()
-> *mut LeanObject {
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    v___x_2833_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__13;
    v___x_2834_ = l_Lean_stringToMessageData(v___x_2833_);
    return v___x_2834_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__16()
-> *mut LeanObject {
    let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    v___x_2836_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__15;
    v___x_2837_ = l_Lean_stringToMessageData(v___x_2836_);
    return v___x_2837_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1(
    mut v_mod_2842_: *mut LeanObject,
    mut v_isMeta_2843_: u8,
    mut v_hint_2844_: *mut LeanObject,
    mut v___y_2845_: *mut LeanObject,
    mut v___y_2846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExporting_2850_: u8 = 0;
    let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entry_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2872_: u8 = 0;
    let mut v_asyncMode_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2882_: u8 = 0;
    let mut v_unused_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: u8 = 0;
    let mut v_options_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2887_: u8 = 0;
    let mut v_inheritedTraceOptions_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cls_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: u8 = 0;
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: u8 = 0;
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2848_ = lean_st_ref_get(v___y_2846_);
                v_env_2849_ = lean_ctor_get(v___x_2848_, 0);
                lean_inc_ref(v_env_2849_);
                lean_dec(v___x_2848_);
                v_isExporting_2850_ = lean_ctor_get_uint8(
                    v_env_2849_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                );
                lean_dec_ref(v_env_2849_);
                v___x_2851_ = lean_st_ref_get(v___y_2846_);
                v_env_2852_ = lean_ctor_get(v___x_2851_, 0);
                lean_inc_ref(v_env_2852_);
                lean_dec(v___x_2851_);
                v___x_2853_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__2);
                lean_inc(v_mod_2842_);
                v_entry_2854_ = lean_alloc_ctor(0, 1, (2) as u32);
                lean_ctor_set(v_entry_2854_, 0, v_mod_2842_);
                lean_ctor_set_uint8(
                    v_entry_2854_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_isExporting_2850_,
                );
                lean_ctor_set_uint8(
                    v_entry_2854_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v_isMeta_2843_,
                );
                v___x_2855_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_2856_ = lean_box(1);
                v___x_2857_ = lean_box(0);
                v___x_2884_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_2853_,
                    v___x_2855_,
                    v_env_2852_,
                    v___x_2856_,
                    v___x_2857_,
                );
                v___x_2885_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v___x_2884_, v_entry_2854_);
                lean_dec(v___x_2884_);
                if v___x_2885_ == 0 {
                    v_options_2886_ = lean_ctor_get(v___y_2845_, 2);
                    v_hasTrace_2887_ = lean_ctor_get_uint8(
                        v_options_2886_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_2887_ == 0 {
                        lean_dec(v_hint_2844_);
                        lean_dec(v_mod_2842_);
                        v___y_2859_ = v___y_2846_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_2888_ = lean_ctor_get(v___y_2845_, 13);
                        v_cls_2889_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__4;
                        v___x_2909_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__12);
                        v___x_2910_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_2888_,
                            v_options_2886_,
                            v___x_2909_,
                        );
                        if v___x_2910_ == 0 {
                            lean_dec(v_hint_2844_);
                            lean_dec(v_mod_2842_);
                            v___y_2859_ = v___y_2846_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2911_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__14_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__14);
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
                    lean_dec_ref_known(v_entry_2854_, 1);
                    lean_dec(v_hint_2844_);
                    lean_dec(v_mod_2842_);
                    v___x_2922_ = lean_box(0);
                    v___x_2923_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2923_, 0, v___x_2922_);
                    return v___x_2923_;
                }
            }
            1 => {
                v___x_2860_ = lean_st_ref_take(v___y_2859_);
                v_toEnvExtension_2861_ = lean_ctor_get(v___x_2855_, 0);
                v_env_2862_ = lean_ctor_get(v___x_2860_, 0);
                v_nextMacroScope_2863_ = lean_ctor_get(v___x_2860_, 1);
                v_ngen_2864_ = lean_ctor_get(v___x_2860_, 2);
                v_auxDeclNGen_2865_ = lean_ctor_get(v___x_2860_, 3);
                v_traceState_2866_ = lean_ctor_get(v___x_2860_, 4);
                v_messages_2867_ = lean_ctor_get(v___x_2860_, 6);
                v_infoState_2868_ = lean_ctor_get(v___x_2860_, 7);
                v_snapshotTasks_2869_ = lean_ctor_get(v___x_2860_, 8);
                v_isSharedCheck_2882_ = (!lean_is_exclusive(v___x_2860_)) as u8;
                if v_isSharedCheck_2882_ == 0 {
                    v_unused_2883_ = lean_ctor_get(v___x_2860_, 5);
                    lean_dec(v_unused_2883_);
                    v___x_2871_ = v___x_2860_;
                    v_isShared_2872_ = v_isSharedCheck_2882_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2869_);
                    lean_inc(v_infoState_2868_);
                    lean_inc(v_messages_2867_);
                    lean_inc(v_traceState_2866_);
                    lean_inc(v_auxDeclNGen_2865_);
                    lean_inc(v_ngen_2864_);
                    lean_inc(v_nextMacroScope_2863_);
                    lean_inc(v_env_2862_);
                    lean_dec(v___x_2860_);
                    v___x_2871_ = lean_box(0);
                    v_isShared_2872_ = v_isSharedCheck_2882_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_2873_ = lean_ctor_get(v_toEnvExtension_2861_, 2);
                v___x_2874_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_2855_,
                    v_env_2862_,
                    v_entry_2854_,
                    v_asyncMode_2873_,
                    v___x_2857_,
                );
                v___x_2875_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_);
                if v_isShared_2872_ == 0 {
                    lean_ctor_set(v___x_2871_, 5, v___x_2875_);
                    lean_ctor_set(v___x_2871_, 0, v___x_2874_);
                    v___x_2877_ = v___x_2871_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2881_, 0, v___x_2874_);
                    lean_ctor_set(v_reuseFailAlloc_2881_, 1, v_nextMacroScope_2863_);
                    lean_ctor_set(v_reuseFailAlloc_2881_, 2, v_ngen_2864_);
                    lean_ctor_set(v_reuseFailAlloc_2881_, 3, v_auxDeclNGen_2865_);
                    lean_ctor_set(v_reuseFailAlloc_2881_, 4, v_traceState_2866_);
                    lean_ctor_set(v_reuseFailAlloc_2881_, 5, v___x_2875_);
                    lean_ctor_set(v_reuseFailAlloc_2881_, 6, v_messages_2867_);
                    lean_ctor_set(v_reuseFailAlloc_2881_, 7, v_infoState_2868_);
                    lean_ctor_set(v_reuseFailAlloc_2881_, 8, v_snapshotTasks_2869_);
                    v___x_2877_ = v_reuseFailAlloc_2881_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2878_ = lean_st_ref_set(v___y_2859_, v___x_2877_);
                v___x_2879_ = lean_box(0);
                v___x_2880_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2880_, 0, v___x_2879_);
                return v___x_2880_;
            }
            4 => {
                v___x_2893_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2893_, 0, v___y_2891_);
                lean_ctor_set(v___x_2893_, 1, v___y_2892_);
                v___x_2894_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__3(v_cls_2889_, v___x_2893_, v___y_2845_, v___y_2846_);
                if lean_obj_tag(v___x_2894_) == 0 {
                    lean_dec_ref_known(v___x_2894_, 1);
                    v___y_2859_ = v___y_2846_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref_known(v_entry_2854_, 1);
                    return v___x_2894_;
                }
            }
            5 => {
                lean_inc_ref(v___y_2897_);
                v___x_2898_ = l_Lean_stringToMessageData(v___y_2897_);
                v___x_2899_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2899_, 0, v___y_2896_);
                lean_ctor_set(v___x_2899_, 1, v___x_2898_);
                v___x_2900_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__6), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__6_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__6);
                v___x_2901_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2901_, 0, v___x_2899_);
                lean_ctor_set(v___x_2901_, 1, v___x_2900_);
                v___x_2902_ = l_Lean_MessageData_ofName(v_mod_2842_);
                v___x_2903_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2903_, 0, v___x_2901_);
                lean_ctor_set(v___x_2903_, 1, v___x_2902_);
                v___x_2904_ = l_Lean_Name_isAnonymous(v_hint_2844_);
                if v___x_2904_ == 0 {
                    v___x_2905_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__8), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__8_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__8);
                    v___x_2906_ = l_Lean_MessageData_ofName(v_hint_2844_);
                    v___x_2907_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2907_, 0, v___x_2905_);
                    lean_ctor_set(v___x_2907_, 1, v___x_2906_);
                    v___y_2891_ = v___x_2903_;
                    v___y_2892_ = v___x_2907_;
                    state = 4;
                    continue;
                } else {
                    lean_dec(v_hint_2844_);
                    v___x_2908_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__9), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__9_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__9);
                    v___y_2891_ = v___x_2903_;
                    v___y_2892_ = v___x_2908_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                lean_inc_ref(v___y_2913_);
                v___x_2914_ = l_Lean_stringToMessageData(v___y_2913_);
                v___x_2915_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2915_, 0, v___x_2911_);
                lean_ctor_set(v___x_2915_, 1, v___x_2914_);
                v___x_2916_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__16), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__16_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1___closed__16);
                v___x_2917_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2917_, 0, v___x_2915_);
                lean_ctor_set(v___x_2917_, 1, v___x_2916_);
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
    mut v_mod_2924_: *mut LeanObject,
    mut v_isMeta_2925_: *mut LeanObject,
    mut v_hint_2926_: *mut LeanObject,
    mut v___y_2927_: *mut LeanObject,
    mut v___y_2928_: *mut LeanObject,
    mut v___y_2929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_2930_: u8 = 0;
    let mut v_res_2931_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_2930_ = (lean_unbox(v_isMeta_2925_) as u8);
    v_res_2931_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1(v_mod_2924_, v_isMeta_boxed_2930_, v_hint_2926_, v___y_2927_, v___y_2928_);
    lean_dec(v___y_2928_);
    lean_dec_ref(v___y_2927_);
    return v_res_2931_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3_spec__6___redArg(
    mut v_a_2932_: *mut LeanObject,
    mut v_x_2933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: u8 = 0;
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2933_) == 0 {
                    v___x_2934_ = lean_box(0);
                    return v___x_2934_;
                } else {
                    v_key_2935_ = lean_ctor_get(v_x_2933_, 0);
                    v_value_2936_ = lean_ctor_get(v_x_2933_, 1);
                    v_tail_2937_ = lean_ctor_get(v_x_2933_, 2);
                    v___x_2938_ = lean_name_eq(v_key_2935_, v_a_2932_);
                    if v___x_2938_ == 0 {
                        v_x_2933_ = v_tail_2937_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_2936_);
                        v___x_2940_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2940_, 0, v_value_2936_);
                        return v___x_2940_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3_spec__6___redArg___boxed(
    mut v_a_2941_: *mut LeanObject,
    mut v_x_2942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2943_: *mut LeanObject = core::ptr::null_mut();
    v_res_2943_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3_spec__6___redArg(v_a_2941_, v_x_2942_);
    lean_dec(v_x_2942_);
    lean_dec(v_a_2941_);
    return v_res_2943_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg___closed__0()
-> u64 {
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: u64 = 0;
    v___x_2944_ = lean_unsigned_to_nat(1723);
    v___x_2945_ = lean_uint64_of_nat(v___x_2944_);
    return v___x_2945_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg(
    mut v_m_2946_: *mut LeanObject,
    mut v_a_2947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: u64 = 0;
    let mut v_hash_2966_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2948_ = lean_ctor_get(v_m_2946_, 1);
                v___x_2949_ = lean_array_get_size(v_buckets_2948_);
                if lean_obj_tag(v_a_2947_) == 0 {
                    v___x_2965_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg___closed__0);
                    v___y_2951_ = v___x_2965_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2966_ = lean_ctor_get_uint64(
                        v_a_2947_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
    mut v_m_2967_: *mut LeanObject,
    mut v_a_2968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2969_: *mut LeanObject = core::ptr::null_mut();
    v_res_2969_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg(v_m_2967_, v_a_2968_);
    lean_dec(v_a_2968_);
    lean_dec_ref(v_m_2967_);
    return v_res_2969_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__2(
    mut v___x_2970_: *mut LeanObject,
    mut v_declName_2971_: *mut LeanObject,
    mut v_as_2972_: *mut LeanObject,
    mut v_sz_2973_: usize,
    mut v_i_2974_: usize,
    mut v_b_2975_: *mut LeanObject,
    mut v___y_2976_: *mut LeanObject,
    mut v___y_2977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2979_: u8 = 0;
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modules_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toImport_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: u8 = 0;
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: usize = 0;
    let mut v___x_2992_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2979_ = lean_usize_dec_lt(v_i_2974_, v_sz_2973_);
                if v___x_2979_ == 0 {
                    lean_dec(v_declName_2971_);
                    v___x_2980_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2980_, 0, v_b_2975_);
                    return v___x_2980_;
                } else {
                    v___x_2981_ = l_Lean_Environment_header(v___x_2970_);
                    v_modules_2982_ = lean_ctor_get(v___x_2981_, 3);
                    lean_inc_ref(v_modules_2982_);
                    lean_dec_ref(v___x_2981_);
                    v___x_2983_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_2984_ = lean_array_uget_borrowed(v_as_2972_, v_i_2974_);
                    v___x_2985_ = lean_array_get(v___x_2983_, v_modules_2982_, v_a_2984_);
                    lean_dec_ref(v_modules_2982_);
                    v_toImport_2986_ = lean_ctor_get(v___x_2985_, 0);
                    lean_inc_ref(v_toImport_2986_);
                    lean_dec(v___x_2985_);
                    v_module_2987_ = lean_ctor_get(v_toImport_2986_, 0);
                    lean_inc(v_module_2987_);
                    lean_dec_ref(v_toImport_2986_);
                    v___x_2988_ = 0;
                    lean_inc(v_declName_2971_);
                    v___x_2989_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1(v_module_2987_, v___x_2988_, v_declName_2971_, v___y_2976_, v___y_2977_);
                    if lean_obj_tag(v___x_2989_) == 0 {
                        lean_dec_ref_known(v___x_2989_, 1);
                        v___x_2990_ = lean_box(0);
                        v___x_2991_ = 1usize;
                        v___x_2992_ = lean_usize_add(v_i_2974_, v___x_2991_);
                        v_i_2974_ = v___x_2992_;
                        v_b_2975_ = v___x_2990_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_declName_2971_);
                        return v___x_2989_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__2___boxed(
    mut v___x_2994_: *mut LeanObject,
    mut v_declName_2995_: *mut LeanObject,
    mut v_as_2996_: *mut LeanObject,
    mut v_sz_2997_: *mut LeanObject,
    mut v_i_2998_: *mut LeanObject,
    mut v_b_2999_: *mut LeanObject,
    mut v___y_3000_: *mut LeanObject,
    mut v___y_3001_: *mut LeanObject,
    mut v___y_3002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3003_: usize = 0;
    let mut v_i_boxed_3004_: usize = 0;
    let mut v_res_3005_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3003_ = lean_unbox_usize(v_sz_2997_);
    lean_dec(v_sz_2997_);
    v_i_boxed_3004_ = lean_unbox_usize(v_i_2998_);
    lean_dec(v_i_2998_);
    v_res_3005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__2(v___x_2994_, v_declName_2995_, v_as_2996_, v_sz_boxed_3003_, v_i_boxed_3004_, v_b_2999_, v___y_3000_, v___y_3001_);
    lean_dec(v___y_3001_);
    lean_dec_ref(v___y_3000_);
    lean_dec_ref(v_as_2996_);
    lean_dec_ref(v___x_2994_);
    return v_res_3005_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__2()
-> *mut LeanObject {
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    v___x_3008_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__1;
    v___x_3009_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__0;
    v___x_3010_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_3009_, v___x_3008_);
    return v___x_3010_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1(
    mut v_declName_3013_: *mut LeanObject,
    mut v_isMeta_3014_: u8,
    mut v___y_3015_: *mut LeanObject,
    mut v___y_3016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3026_: usize = 0;
    let mut v___x_3027_: usize = 0;
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3031_: u8 = 0;
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3035_: u8 = 0;
    let mut v_unused_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modules_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: u8 = 0;
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3048_: u8 = 0;
    let mut v_toImport_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: u8 = 0;
    let mut v___x_3060_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3018_ = lean_st_ref_get(v___y_3016_);
                v_env_3022_ = lean_ctor_get(v___x_3018_, 0);
                lean_inc_ref(v_env_3022_);
                lean_dec(v___x_3018_);
                v___x_3037_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3022_, v_declName_3013_);
                if lean_obj_tag(v___x_3037_) == 0 {
                    lean_dec_ref(v_env_3022_);
                    lean_dec(v_declName_3013_);
                    state = 1;
                    continue;
                } else {
                    v_val_3038_ = lean_ctor_get(v___x_3037_, 0);
                    lean_inc(v_val_3038_);
                    lean_dec_ref_known(v___x_3037_, 1);
                    v___x_3039_ = l_Lean_Environment_header(v_env_3022_);
                    v_modules_3040_ = lean_ctor_get(v___x_3039_, 3);
                    lean_inc_ref(v_modules_3040_);
                    lean_dec_ref(v___x_3039_);
                    v___x_3041_ = lean_array_get_size(v_modules_3040_);
                    v___x_3042_ = lean_nat_dec_lt(v_val_3038_, v___x_3041_);
                    if v___x_3042_ == 0 {
                        lean_dec_ref(v_modules_3040_);
                        lean_dec(v_val_3038_);
                        lean_dec_ref(v_env_3022_);
                        lean_dec(v_declName_3013_);
                        state = 1;
                        continue;
                    } else {
                        v___x_3043_ = lean_st_ref_get(v___y_3016_);
                        v_env_3044_ = lean_ctor_get(v___x_3043_, 0);
                        lean_inc_ref(v_env_3044_);
                        lean_dec(v___x_3043_);
                        v___x_3045_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__2);
                        v___x_3046_ = lean_array_fget(v_modules_3040_, v_val_3038_);
                        lean_dec(v_val_3038_);
                        lean_dec_ref(v_modules_3040_);
                        if v_isMeta_3014_ == 0 {
                            lean_dec_ref(v_env_3044_);
                            v___y_3048_ = v_isMeta_3014_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_declName_3013_);
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
                v___x_3020_ = lean_box(0);
                v___x_3021_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3021_, 0, v___x_3020_);
                return v___x_3021_;
            }
            2 => {
                v___x_3025_ = lean_box(0);
                v_sz_3026_ = lean_array_size(v___y_3024_);
                v___x_3027_ = 0usize;
                v___x_3028_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__2(v_env_3022_, v_declName_3013_, v___y_3024_, v_sz_3026_, v___x_3027_, v___x_3025_, v___y_3015_, v___y_3016_);
                lean_dec_ref(v___y_3024_);
                lean_dec_ref(v_env_3022_);
                if lean_obj_tag(v___x_3028_) == 0 {
                    v_isSharedCheck_3035_ = (!lean_is_exclusive(v___x_3028_)) as u8;
                    if v_isSharedCheck_3035_ == 0 {
                        v_unused_3036_ = lean_ctor_get(v___x_3028_, 0);
                        lean_dec(v_unused_3036_);
                        v___x_3030_ = v___x_3028_;
                        v_isShared_3031_ = v_isSharedCheck_3035_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_3028_);
                        v___x_3030_ = lean_box(0);
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
                    lean_ctor_set(v___x_3030_, 0, v___x_3025_);
                    v___x_3033_ = v___x_3030_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3034_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3034_, 0, v___x_3025_);
                    v___x_3033_ = v_reuseFailAlloc_3034_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3033_;
            }
            5 => {
                v_toImport_3049_ = lean_ctor_get(v___x_3046_, 0);
                lean_inc_ref(v_toImport_3049_);
                lean_dec(v___x_3046_);
                v_module_3050_ = lean_ctor_get(v_toImport_3049_, 0);
                lean_inc(v_module_3050_);
                lean_dec_ref(v_toImport_3049_);
                lean_inc(v_declName_3013_);
                v___x_3051_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1(v_module_3050_, v___y_3048_, v_declName_3013_, v___y_3015_, v___y_3016_);
                if lean_obj_tag(v___x_3051_) == 0 {
                    lean_dec_ref_known(v___x_3051_, 1);
                    v___x_3052_ = l_Lean_indirectModUseExt;
                    v___x_3053_ = lean_box(1);
                    v___x_3054_ = lean_box(0);
                    lean_inc_ref(v_env_3022_);
                    v___x_3055_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_3045_,
                        v___x_3052_,
                        v_env_3022_,
                        v___x_3053_,
                        v___x_3054_,
                    );
                    v___x_3056_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg(v___x_3055_, v_declName_3013_);
                    lean_dec(v___x_3055_);
                    if lean_obj_tag(v___x_3056_) == 0 {
                        v___x_3057_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___closed__3;
                        v___y_3024_ = v___x_3057_;
                        state = 2;
                        continue;
                    } else {
                        v_val_3058_ = lean_ctor_get(v___x_3056_, 0);
                        lean_inc(v_val_3058_);
                        lean_dec_ref_known(v___x_3056_, 1);
                        v___y_3024_ = v_val_3058_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_env_3022_);
                    lean_dec(v_declName_3013_);
                    return v___x_3051_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1___boxed(
    mut v_declName_3061_: *mut LeanObject,
    mut v_isMeta_3062_: *mut LeanObject,
    mut v___y_3063_: *mut LeanObject,
    mut v___y_3064_: *mut LeanObject,
    mut v___y_3065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_3066_: u8 = 0;
    let mut v_res_3067_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_3066_ = (lean_unbox(v_isMeta_3062_) as u8);
    v_res_3067_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1(v_declName_3061_, v_isMeta_boxed_3066_, v___y_3063_, v___y_3064_);
    lean_dec(v___y_3064_);
    lean_dec_ref(v___y_3063_);
    return v_res_3067_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__2(
    mut v___y_3068_: u8,
    mut v_as_3069_: *mut LeanObject,
    mut v_i_3070_: usize,
    mut v_stop_3071_: usize,
    mut v_b_3072_: *mut LeanObject,
    mut v___y_3073_: *mut LeanObject,
    mut v___y_3074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3076_: u8 = 0;
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: usize = 0;
    let mut v___x_3081_: usize = 0;
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3076_ = lean_usize_dec_eq(v_i_3070_, v_stop_3071_);
                if v___x_3076_ == 0 {
                    v___x_3077_ = lean_array_uget_borrowed(v_as_3069_, v_i_3070_);
                    lean_inc(v___x_3077_);
                    v___x_3078_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1(v___x_3077_, v___y_3068_, v___y_3073_, v___y_3074_);
                    if lean_obj_tag(v___x_3078_) == 0 {
                        v_a_3079_ = lean_ctor_get(v___x_3078_, 0);
                        lean_inc(v_a_3079_);
                        lean_dec_ref_known(v___x_3078_, 1);
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
                    v___x_3083_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3083_, 0, v_b_3072_);
                    return v___x_3083_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__2___boxed(
    mut v___y_3084_: *mut LeanObject,
    mut v_as_3085_: *mut LeanObject,
    mut v_i_3086_: *mut LeanObject,
    mut v_stop_3087_: *mut LeanObject,
    mut v_b_3088_: *mut LeanObject,
    mut v___y_3089_: *mut LeanObject,
    mut v___y_3090_: *mut LeanObject,
    mut v___y_3091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6748__boxed_3092_: u8 = 0;
    let mut v_i_boxed_3093_: usize = 0;
    let mut v_stop_boxed_3094_: usize = 0;
    let mut v_res_3095_: *mut LeanObject = core::ptr::null_mut();
    v___y_6748__boxed_3092_ = (lean_unbox(v___y_3084_) as u8);
    v_i_boxed_3093_ = lean_unbox_usize(v_i_3086_);
    lean_dec(v_i_3086_);
    v_stop_boxed_3094_ = lean_unbox_usize(v_stop_3087_);
    lean_dec(v_stop_3087_);
    v_res_3095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__2(v___y_6748__boxed_3092_, v_as_3085_, v_i_boxed_3093_, v_stop_boxed_3094_, v_b_3088_, v___y_3089_, v___y_3090_);
    lean_dec(v___y_3090_);
    lean_dec_ref(v___y_3089_);
    lean_dec_ref(v_as_3085_);
    return v_res_3095_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__0(
    mut v_sz_3096_: usize,
    mut v_i_3097_: usize,
    mut v_bs_3098_: *mut LeanObject,
    mut v___y_3099_: *mut LeanObject,
    mut v___y_3100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3102_: u8 = 0;
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: usize = 0;
    let mut v___x_3111_: usize = 0;
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3117_: u8 = 0;
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3121_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3102_ = lean_usize_dec_lt(v_i_3097_, v_sz_3096_);
                if v___x_3102_ == 0 {
                    v___x_3103_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3103_, 0, v_bs_3098_);
                    return v___x_3103_;
                } else {
                    v_v_3104_ = lean_array_uget_borrowed(v_bs_3098_, v_i_3097_);
                    v___x_3105_ = lean_box(0);
                    lean_inc(v_v_3104_);
                    v___x_3106_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(
                        v_v_3104_,
                        v___x_3105_,
                        v___y_3099_,
                        v___y_3100_,
                    );
                    if lean_obj_tag(v___x_3106_) == 0 {
                        v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
                        lean_inc(v_a_3107_);
                        lean_dec_ref_known(v___x_3106_, 1);
                        v___x_3108_ = lean_unsigned_to_nat(0);
                        v_bs_x27_3109_ = lean_array_uset(v_bs_3098_, v_i_3097_, v___x_3108_);
                        v___x_3110_ = 1usize;
                        v___x_3111_ = lean_usize_add(v_i_3097_, v___x_3110_);
                        v___x_3112_ = lean_array_uset(v_bs_x27_3109_, v_i_3097_, v_a_3107_);
                        v_i_3097_ = v___x_3111_;
                        v_bs_3098_ = v___x_3112_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_3098_);
                        v_a_3114_ = lean_ctor_get(v___x_3106_, 0);
                        v_isSharedCheck_3121_ = (!lean_is_exclusive(v___x_3106_)) as u8;
                        if v_isSharedCheck_3121_ == 0 {
                            v___x_3116_ = v___x_3106_;
                            v_isShared_3117_ = v_isSharedCheck_3121_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3114_);
                            lean_dec(v___x_3106_);
                            v___x_3116_ = lean_box(0);
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
                    v_reuseFailAlloc_3120_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_a_3114_);
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
    mut v_sz_3122_: *mut LeanObject,
    mut v_i_3123_: *mut LeanObject,
    mut v_bs_3124_: *mut LeanObject,
    mut v___y_3125_: *mut LeanObject,
    mut v___y_3126_: *mut LeanObject,
    mut v___y_3127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3128_: usize = 0;
    let mut v_i_boxed_3129_: usize = 0;
    let mut v_res_3130_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3128_ = lean_unbox_usize(v_sz_3122_);
    lean_dec(v_sz_3122_);
    v_i_boxed_3129_ = lean_unbox_usize(v_i_3123_);
    lean_dec(v_i_3123_);
    v_res_3130_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__0(v_sz_boxed_3128_, v_i_boxed_3129_, v_bs_3124_, v___y_3125_, v___y_3126_);
    lean_dec(v___y_3126_);
    lean_dec_ref(v___y_3125_);
    return v_res_3130_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_(
    mut v___x_3131_: *mut LeanObject,
    mut v___x_3132_: *mut LeanObject,
    mut v___x_3133_: *mut LeanObject,
    mut v___x_3134_: *mut LeanObject,
    mut v___x_3135_: *mut LeanObject,
    mut v_decl_3136_: *mut LeanObject,
    mut v_stx_3137_: *mut LeanObject,
    mut v_kind_3138_: u8,
    mut v___y_3139_: *mut LeanObject,
    mut v___y_3140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3155_: u8 = 0;
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3167_: u8 = 0;
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3183_: u8 = 0;
    let mut v_unused_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3185_: u8 = 0;
    let mut v_a_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3189_: u8 = 0;
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3197_: u8 = 0;
    let mut v___y_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3206_: usize = 0;
    let mut v___y_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3208_: u8 = 0;
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: u8 = 0;
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: u8 = 0;
    let mut v___x_3213_: usize = 0;
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: usize = 0;
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3221_: u8 = 0;
    let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: u8 = 0;
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3231_: usize = 0;
    let mut v___x_3232_: usize = 0;
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3237_: u8 = 0;
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: u8 = 0;
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3246_: u8 = 0;
    let mut v_a_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3250_: u8 = 0;
    let mut v___x_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3254_: u8 = 0;
    let mut v_isSharedCheck_3255_: u8 = 0;
    let mut v_unused_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: u8 = 0;
    let mut v___x_3258_: u8 = 0;
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3257_ = 0;
                v___x_3258_ = l_Lean_instBEqAttributeKind_beq(v_kind_3138_, v___x_3257_);
                if v___x_3258_ == 0 {
                    lean_dec(v_stx_3137_);
                    lean_dec(v_decl_3136_);
                    lean_dec_ref(v___x_3135_);
                    lean_dec_ref(v___x_3134_);
                    lean_dec(v___x_3131_);
                    v___x_3259_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__1___redArg(v___x_3133_, v_kind_3138_, v___y_3139_, v___y_3140_);
                    return v___x_3259_;
                } else {
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_3146_ = lean_st_ref_get(v___y_3144_);
                v_env_3147_ = lean_ctor_get(v___x_3146_, 0);
                lean_inc_ref(v_env_3147_);
                lean_dec(v___x_3146_);
                v_options_3148_ = lean_ctor_get(v___y_3143_, 2);
                v_ref_3149_ = lean_ctor_get(v___y_3143_, 5);
                lean_inc_ref(v_options_3148_);
                v___x_3150_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3150_, 0, v_env_3147_);
                lean_ctor_set(v___x_3150_, 1, v_options_3148_);
                lean_inc(v_decl_3136_);
                v___x_3151_ = l_Lean_CodeAction_mkCommandCodeAction(v_decl_3136_, v___x_3150_);
                lean_dec_ref_known(v___x_3150_, 2);
                if lean_obj_tag(v___x_3151_) == 0 {
                    v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
                    v_isSharedCheck_3185_ = (!lean_is_exclusive(v___x_3151_)) as u8;
                    if v_isSharedCheck_3185_ == 0 {
                        v___x_3154_ = v___x_3151_;
                        v_isShared_3155_ = v_isSharedCheck_3185_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3152_);
                        lean_dec(v___x_3151_);
                        v___x_3154_ = lean_box(0);
                        v_isShared_3155_ = v_isSharedCheck_3185_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_3145_);
                    lean_dec(v_decl_3136_);
                    lean_dec(v___x_3131_);
                    v_a_3186_ = lean_ctor_get(v___x_3151_, 0);
                    v_isSharedCheck_3197_ = (!lean_is_exclusive(v___x_3151_)) as u8;
                    if v_isSharedCheck_3197_ == 0 {
                        v___x_3188_ = v___x_3151_;
                        v_isShared_3189_ = v_isSharedCheck_3197_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3186_);
                        lean_dec(v___x_3151_);
                        v___x_3188_ = lean_box(0);
                        v_isShared_3189_ = v_isSharedCheck_3197_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3156_ = lean_st_ref_take(v___y_3144_);
                v_env_3157_ = lean_ctor_get(v___x_3156_, 0);
                v_nextMacroScope_3158_ = lean_ctor_get(v___x_3156_, 1);
                v_ngen_3159_ = lean_ctor_get(v___x_3156_, 2);
                v_auxDeclNGen_3160_ = lean_ctor_get(v___x_3156_, 3);
                v_traceState_3161_ = lean_ctor_get(v___x_3156_, 4);
                v_messages_3162_ = lean_ctor_get(v___x_3156_, 6);
                v_infoState_3163_ = lean_ctor_get(v___x_3156_, 7);
                v_snapshotTasks_3164_ = lean_ctor_get(v___x_3156_, 8);
                v_isSharedCheck_3183_ = (!lean_is_exclusive(v___x_3156_)) as u8;
                if v_isSharedCheck_3183_ == 0 {
                    v_unused_3184_ = lean_ctor_get(v___x_3156_, 5);
                    lean_dec(v_unused_3184_);
                    v___x_3166_ = v___x_3156_;
                    v_isShared_3167_ = v_isSharedCheck_3183_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3164_);
                    lean_inc(v_infoState_3163_);
                    lean_inc(v_messages_3162_);
                    lean_inc(v_traceState_3161_);
                    lean_inc(v_auxDeclNGen_3160_);
                    lean_inc(v_ngen_3159_);
                    lean_inc(v_nextMacroScope_3158_);
                    lean_inc(v_env_3157_);
                    lean_dec(v___x_3156_);
                    v___x_3166_ = lean_box(0);
                    v_isShared_3167_ = v_isSharedCheck_3183_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3168_ = l_Lean_CodeAction_cmdCodeActionExt;
                v_toEnvExtension_3169_ = lean_ctor_get(v___x_3168_, 0);
                v_asyncMode_3170_ = lean_ctor_get(v_toEnvExtension_3169_, 2);
                v___x_3171_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3171_, 0, v_decl_3136_);
                lean_ctor_set(v___x_3171_, 1, v___y_3145_);
                v___x_3172_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3172_, 0, v___x_3171_);
                lean_ctor_set(v___x_3172_, 1, v_a_3152_);
                v___x_3173_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_3168_,
                    v_env_3157_,
                    v___x_3172_,
                    v_asyncMode_3170_,
                    v___x_3131_,
                );
                v___x_3174_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__2_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_);
                if v_isShared_3167_ == 0 {
                    lean_ctor_set(v___x_3166_, 5, v___x_3174_);
                    lean_ctor_set(v___x_3166_, 0, v___x_3173_);
                    v___x_3176_ = v___x_3166_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3173_);
                    lean_ctor_set(v_reuseFailAlloc_3182_, 1, v_nextMacroScope_3158_);
                    lean_ctor_set(v_reuseFailAlloc_3182_, 2, v_ngen_3159_);
                    lean_ctor_set(v_reuseFailAlloc_3182_, 3, v_auxDeclNGen_3160_);
                    lean_ctor_set(v_reuseFailAlloc_3182_, 4, v_traceState_3161_);
                    lean_ctor_set(v_reuseFailAlloc_3182_, 5, v___x_3174_);
                    lean_ctor_set(v_reuseFailAlloc_3182_, 6, v_messages_3162_);
                    lean_ctor_set(v_reuseFailAlloc_3182_, 7, v_infoState_3163_);
                    lean_ctor_set(v_reuseFailAlloc_3182_, 8, v_snapshotTasks_3164_);
                    v___x_3176_ = v_reuseFailAlloc_3182_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3177_ = lean_st_ref_set(v___y_3144_, v___x_3176_);
                v___x_3178_ = lean_box(0);
                if v_isShared_3155_ == 0 {
                    lean_ctor_set(v___x_3154_, 0, v___x_3178_);
                    v___x_3180_ = v___x_3154_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3181_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3181_, 0, v___x_3178_);
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
                v___x_3191_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_3191_, 0, v___x_3190_);
                v___x_3192_ = l_Lean_MessageData_ofFormat(v___x_3191_);
                lean_inc(v_ref_3149_);
                v___x_3193_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3193_, 0, v_ref_3149_);
                lean_ctor_set(v___x_3193_, 1, v___x_3192_);
                if v_isShared_3189_ == 0 {
                    lean_ctor_set(v___x_3188_, 0, v___x_3193_);
                    v___x_3195_ = v___x_3188_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3196_, 0, v___x_3193_);
                    v___x_3195_ = v_reuseFailAlloc_3196_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3195_;
            }
            8 => {
                if lean_obj_tag(v___y_3202_) == 0 {
                    lean_dec_ref_known(v___y_3202_, 1);
                    v___y_3143_ = v___y_3199_;
                    v___y_3144_ = v___y_3200_;
                    v___y_3145_ = v___y_3201_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v___y_3201_);
                    lean_dec(v_decl_3136_);
                    lean_dec(v___x_3131_);
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
                    v___x_3211_ = lean_box(0);
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
                lean_inc(v_decl_3136_);
                v___x_3218_ = l_Lean_ensureAttrDeclIsMeta(
                    v___x_3133_,
                    v_decl_3136_,
                    v_kind_3138_,
                    v___y_3139_,
                    v___y_3140_,
                );
                if lean_obj_tag(v___x_3218_) == 0 {
                    v_isSharedCheck_3255_ = (!lean_is_exclusive(v___x_3218_)) as u8;
                    if v_isSharedCheck_3255_ == 0 {
                        v_unused_3256_ = lean_ctor_get(v___x_3218_, 0);
                        lean_dec(v_unused_3256_);
                        v___x_3220_ = v___x_3218_;
                        v_isShared_3221_ = v_isSharedCheck_3255_;
                        state = 11;
                        continue;
                    } else {
                        lean_dec(v___x_3218_);
                        v___x_3220_ = lean_box(0);
                        v_isShared_3221_ = v_isSharedCheck_3255_;
                        state = 11;
                        continue;
                    }
                } else {
                    lean_dec(v_stx_3137_);
                    lean_dec(v_decl_3136_);
                    lean_dec_ref(v___x_3135_);
                    lean_dec_ref(v___x_3134_);
                    lean_dec(v___x_3131_);
                    return v___x_3218_;
                }
            }
            11 => {
                v___x_3222_ = l_Lean_Name_mkStr2(v___x_3134_, v___x_3135_);
                lean_inc(v_stx_3137_);
                v___x_3223_ = l_Lean_Syntax_isOfKind(v_stx_3137_, v___x_3222_);
                lean_dec(v___x_3222_);
                if v___x_3223_ == 0 {
                    lean_dec(v_stx_3137_);
                    lean_dec(v_decl_3136_);
                    lean_dec(v___x_3131_);
                    v___x_3224_ = lean_box(0);
                    if v_isShared_3221_ == 0 {
                        lean_ctor_set(v___x_3220_, 0, v___x_3224_);
                        v___x_3226_ = v___x_3220_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3227_, 0, v___x_3224_);
                        v___x_3226_ = v_reuseFailAlloc_3227_;
                        state = 12;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3220_);
                    v___x_3228_ = lean_unsigned_to_nat(1);
                    v___x_3229_ = l_Lean_Syntax_getArg(v_stx_3137_, v___x_3228_);
                    lean_dec(v_stx_3137_);
                    v___x_3230_ = l_Lean_Syntax_getArgs(v___x_3229_);
                    lean_dec(v___x_3229_);
                    v_sz_3231_ = lean_array_size(v___x_3230_);
                    v___x_3232_ = 0usize;
                    v___x_3233_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__0(v_sz_3231_, v___x_3232_, v___x_3230_, v___y_3139_, v___y_3140_);
                    if lean_obj_tag(v___x_3233_) == 0 {
                        v_a_3234_ = lean_ctor_get(v___x_3233_, 0);
                        v_isSharedCheck_3246_ = (!lean_is_exclusive(v___x_3233_)) as u8;
                        if v_isSharedCheck_3246_ == 0 {
                            v___x_3236_ = v___x_3233_;
                            v_isShared_3237_ = v_isSharedCheck_3246_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_3234_);
                            lean_dec(v___x_3233_);
                            v___x_3236_ = lean_box(0);
                            v_isShared_3237_ = v_isSharedCheck_3246_;
                            state = 13;
                            continue;
                        }
                    } else {
                        lean_dec(v_decl_3136_);
                        lean_dec(v___x_3131_);
                        v_a_3247_ = lean_ctor_get(v___x_3233_, 0);
                        v_isSharedCheck_3254_ = (!lean_is_exclusive(v___x_3233_)) as u8;
                        if v_isSharedCheck_3254_ == 0 {
                            v___x_3249_ = v___x_3233_;
                            v_isShared_3250_ = v_isSharedCheck_3254_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_3247_);
                            lean_dec(v___x_3233_);
                            v___x_3249_ = lean_box(0);
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
                v_env_3239_ = lean_ctor_get(v___x_3238_, 0);
                lean_inc_ref(v_env_3239_);
                lean_dec(v___x_3238_);
                lean_inc(v_decl_3136_);
                v___x_3240_ = lean_decl_get_sorry_dep(v_env_3239_, v_decl_3136_);
                if lean_obj_tag(v___x_3240_) == 0 {
                    lean_del_object(v___x_3236_);
                    v___x_3241_ = 0;
                    v___y_3204_ = v___y_3139_;
                    v___y_3205_ = v___y_3140_;
                    v___y_3206_ = v___x_3232_;
                    v___y_3207_ = v_a_3234_;
                    v___y_3208_ = v___x_3241_;
                    state = 9;
                    continue;
                } else {
                    lean_dec_ref_known(v___x_3240_, 1);
                    if v___x_3223_ == 0 {
                        lean_del_object(v___x_3236_);
                        v___y_3204_ = v___y_3139_;
                        v___y_3205_ = v___y_3140_;
                        v___y_3206_ = v___x_3232_;
                        v___y_3207_ = v_a_3234_;
                        v___y_3208_ = v___x_3223_;
                        state = 9;
                        continue;
                    } else {
                        lean_dec(v_a_3234_);
                        lean_dec(v_decl_3136_);
                        lean_dec(v___x_3131_);
                        v___x_3242_ = lean_box(0);
                        if v_isShared_3237_ == 0 {
                            lean_ctor_set(v___x_3236_, 0, v___x_3242_);
                            v___x_3244_ = v___x_3236_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3245_, 0, v___x_3242_);
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
                    v_reuseFailAlloc_3253_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_a_3247_);
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
    mut v___x_3260_: *mut LeanObject,
    mut v___x_3261_: *mut LeanObject,
    mut v___x_3262_: *mut LeanObject,
    mut v___x_3263_: *mut LeanObject,
    mut v___x_3264_: *mut LeanObject,
    mut v_decl_3265_: *mut LeanObject,
    mut v_stx_3266_: *mut LeanObject,
    mut v_kind_3267_: *mut LeanObject,
    mut v___y_3268_: *mut LeanObject,
    mut v___y_3269_: *mut LeanObject,
    mut v___y_3270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_3271_: u8 = 0;
    let mut v_res_3272_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_3271_ = (lean_unbox(v_kind_3267_) as u8);
    v_res_3272_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_(v___x_3260_, v___x_3261_, v___x_3262_, v___x_3263_, v___x_3264_, v_decl_3265_, v_stx_3266_, v_kind_boxed_3271_, v___y_3268_, v___y_3269_);
    lean_dec(v___y_3269_);
    lean_dec_ref(v___y_3268_);
    lean_dec(v___x_3261_);
    return v_res_3272_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_(
    mut v___x_3273_: *mut LeanObject,
    mut v_decl_3274_: *mut LeanObject,
    mut v___y_3275_: *mut LeanObject,
    mut v___y_3276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    v___x_3278_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__1_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_);
    v___x_3279_ = l_Lean_MessageData_ofName(v___x_3273_);
    v___x_3280_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3280_, 0, v___x_3278_);
    lean_ctor_set(v___x_3280_, 1, v___x_3279_);
    v___x_3281_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1___closed__3_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_);
    v___x_3282_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3282_, 0, v___x_3280_);
    lean_ctor_set(v___x_3282_, 1, v___x_3281_);
    v___x_3283_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0___redArg(v___x_3282_, v___y_3275_, v___y_3276_);
    return v___x_3283_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2____boxed(
    mut v___x_3284_: *mut LeanObject,
    mut v_decl_3285_: *mut LeanObject,
    mut v___y_3286_: *mut LeanObject,
    mut v___y_3287_: *mut LeanObject,
    mut v___y_3288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3289_: *mut LeanObject = core::ptr::null_mut();
    v_res_3289_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__1_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_(v___x_3284_, v_decl_3285_, v___y_3286_, v___y_3287_);
    lean_dec(v___y_3287_);
    lean_dec_ref(v___y_3286_);
    lean_dec(v_decl_3285_);
    return v_res_3289_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    v___x_3324_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_;
    v___x_3325_ = l_Lean_registerBuiltinAttribute(v___x_3324_);
    return v___x_3325_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2____boxed(
    mut v_a_3326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3327_: *mut LeanObject = core::ptr::null_mut();
    v_res_3327_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_();
    return v_res_3327_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3(
    mut v_00_u03b2_3328_: *mut LeanObject,
    mut v_m_3329_: *mut LeanObject,
    mut v_a_3330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3331_: *mut LeanObject = core::ptr::null_mut();
    v___x_3331_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___redArg(v_m_3329_, v_a_3330_);
    return v___x_3331_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3___boxed(
    mut v_00_u03b2_3332_: *mut LeanObject,
    mut v_m_3333_: *mut LeanObject,
    mut v_a_3334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3335_: *mut LeanObject = core::ptr::null_mut();
    v_res_3335_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3(v_00_u03b2_3332_, v_m_3333_, v_a_3334_);
    lean_dec(v_a_3334_);
    lean_dec_ref(v_m_3333_);
    return v_res_3335_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2(
    mut v_00_u03b2_3336_: *mut LeanObject,
    mut v_x_3337_: *mut LeanObject,
    mut v_x_3338_: *mut LeanObject,
) -> u8 {
    let mut v___x_3339_: u8 = 0;
    v___x_3339_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v_x_3337_, v_x_3338_);
    return v___x_3339_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(
    mut v_00_u03b2_3340_: *mut LeanObject,
    mut v_x_3341_: *mut LeanObject,
    mut v_x_3342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3343_: u8 = 0;
    let mut v_r_3344_: *mut LeanObject = core::ptr::null_mut();
    v_res_3343_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_00_u03b2_3340_, v_x_3341_, v_x_3342_);
    lean_dec_ref(v_x_3342_);
    lean_dec_ref(v_x_3341_);
    v_r_3344_ = lean_box((v_res_3343_) as usize);
    return v_r_3344_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3_spec__6(
    mut v_00_u03b2_3345_: *mut LeanObject,
    mut v_a_3346_: *mut LeanObject,
    mut v_x_3347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    v___x_3348_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3_spec__6___redArg(v_a_3346_, v_x_3347_);
    return v___x_3348_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3_spec__6___boxed(
    mut v_00_u03b2_3349_: *mut LeanObject,
    mut v_a_3350_: *mut LeanObject,
    mut v_x_3351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3352_: *mut LeanObject = core::ptr::null_mut();
    v_res_3352_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__3_spec__6(v_00_u03b2_3349_, v_a_3350_, v_x_3351_);
    lean_dec(v_x_3351_);
    lean_dec(v_a_3350_);
    return v_res_3352_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4(
    mut v_00_u03b2_3353_: *mut LeanObject,
    mut v_x_3354_: *mut LeanObject,
    mut v_x_3355_: usize,
    mut v_x_3356_: *mut LeanObject,
) -> u8 {
    let mut v___x_3357_: u8 = 0;
    v___x_3357_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg(v_x_3354_, v_x_3355_, v_x_3356_);
    return v___x_3357_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b2_3358_: *mut LeanObject,
    mut v_x_3359_: *mut LeanObject,
    mut v_x_3360_: *mut LeanObject,
    mut v_x_3361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_7272__boxed_3362_: usize = 0;
    let mut v_res_3363_: u8 = 0;
    let mut v_r_3364_: *mut LeanObject = core::ptr::null_mut();
    v_x_7272__boxed_3362_ = lean_unbox_usize(v_x_3360_);
    lean_dec(v_x_3360_);
    v_res_3363_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4(v_00_u03b2_3358_, v_x_3359_, v_x_7272__boxed_3362_, v_x_3361_);
    lean_dec_ref(v_x_3361_);
    lean_dec_ref(v_x_3359_);
    v_r_3364_ = lean_box((v_res_3363_) as usize);
    return v_r_3364_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4_spec__7(
    mut v_00_u03b2_3365_: *mut LeanObject,
    mut v_keys_3366_: *mut LeanObject,
    mut v_vals_3367_: *mut LeanObject,
    mut v_heq_3368_: *mut LeanObject,
    mut v_i_3369_: *mut LeanObject,
    mut v_k_3370_: *mut LeanObject,
) -> u8 {
    let mut v___x_3371_: u8 = 0;
    v___x_3371_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4_spec__7___redArg(v_keys_3366_, v_i_3369_, v_k_3370_);
    return v___x_3371_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4_spec__7___boxed(
    mut v_00_u03b2_3372_: *mut LeanObject,
    mut v_keys_3373_: *mut LeanObject,
    mut v_vals_3374_: *mut LeanObject,
    mut v_heq_3375_: *mut LeanObject,
    mut v_i_3376_: *mut LeanObject,
    mut v_k_3377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3378_: u8 = 0;
    let mut v_r_3379_: *mut LeanObject = core::ptr::null_mut();
    v_res_3378_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4_spec__7(v_00_u03b2_3372_, v_keys_3373_, v_vals_3374_, v_heq_3375_, v_i_3376_, v_k_3377_);
    lean_dec_ref(v_k_3377_);
    lean_dec_ref(v_vals_3374_);
    lean_dec_ref(v_keys_3373_);
    v_r_3379_ = lean_box((v_res_3378_) as usize);
    return v_r_3379_;
}
pub unsafe fn l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin_spec__0(
    mut v_nilFn_3380_: *mut LeanObject,
    mut v_consFn_3381_: *mut LeanObject,
    mut v_x_3382_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_3382_) == 0 {
        lean_dec_ref(v_consFn_3381_);
        lean_inc_ref(v_nilFn_3380_);
        return v_nilFn_3380_;
    } else {
        let mut v_head_3383_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_3384_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
        v_head_3383_ = lean_ctor_get(v_x_3382_, 0);
        lean_inc(v_head_3383_);
        v_tail_3384_ = lean_ctor_get(v_x_3382_, 1);
        lean_inc(v_tail_3384_);
        lean_dec_ref_known(v_x_3382_, 2);
        v___x_3385_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_head_3383_);
        lean_inc_ref(v_consFn_3381_);
        v___x_3386_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin_spec__0(v_nilFn_3380_, v_consFn_3381_, v_tail_3384_);
        v___x_3387_ = l_Lean_mkAppB(v_consFn_3381_, v___x_3385_, v___x_3386_);
        return v___x_3387_;
    }
}
pub unsafe fn l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin_spec__0___boxed(
    mut v_nilFn_3388_: *mut LeanObject,
    mut v_consFn_3389_: *mut LeanObject,
    mut v_x_3390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3391_: *mut LeanObject = core::ptr::null_mut();
    v_res_3391_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin_spec__0(v_nilFn_3388_, v_consFn_3389_, v_x_3390_);
    lean_dec_ref(v_nilFn_3388_);
    return v_res_3391_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__2()
-> *mut LeanObject {
    let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    v___x_3397_ = lean_box(0);
    v___x_3398_ =
        l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__1;
    v___x_3399_ = l_Lean_mkConst(v___x_3398_, v___x_3397_);
    return v___x_3399_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5()
-> *mut LeanObject {
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3406_: *mut LeanObject = core::ptr::null_mut();
    v___x_3404_ = lean_box(0);
    v___x_3405_ =
        l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__4;
    v_type_3406_ = l_Lean_mkConst(v___x_3405_, v___x_3404_);
    return v_type_3406_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__10()
-> *mut LeanObject {
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    v___x_3415_ =
        l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__9;
    v___x_3416_ =
        l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__8;
    v___x_3417_ = l_Lean_mkConst(v___x_3416_, v___x_3415_);
    return v___x_3417_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__11()
-> *mut LeanObject {
    let mut v___x_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut LeanObject = core::ptr::null_mut();
    v___x_3418_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1);
    v___x_3419_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_3419_, 0, v___x_3418_);
    lean_ctor_set(v___x_3419_, 1, v___x_3418_);
    lean_ctor_set(v___x_3419_, 2, v___x_3418_);
    lean_ctor_set(v___x_3419_, 3, v___x_3418_);
    lean_ctor_set(v___x_3419_, 4, v___x_3418_);
    lean_ctor_set(v___x_3419_, 5, v___x_3418_);
    return v___x_3419_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__12()
-> *mut LeanObject {
    let mut v___x_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut LeanObject = core::ptr::null_mut();
    v___x_3420_ = lean_unsigned_to_nat(32);
    v___x_3421_ = lean_mk_empty_array_with_capacity(v___x_3420_);
    v___x_3422_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3422_, 0, v___x_3421_);
    return v___x_3422_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__13()
-> *mut LeanObject {
    let mut v___x_3423_: usize = 0;
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut LeanObject = core::ptr::null_mut();
    v___x_3423_ = 5usize;
    v___x_3424_ = lean_unsigned_to_nat(0);
    v___x_3425_ = lean_unsigned_to_nat(32);
    v___x_3426_ = lean_mk_empty_array_with_capacity(v___x_3425_);
    v___x_3427_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__12_once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__12);
    v___x_3428_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_3428_, 0, v___x_3427_);
    lean_ctor_set(v___x_3428_, 1, v___x_3426_);
    lean_ctor_set(v___x_3428_, 2, v___x_3424_);
    lean_ctor_set(v___x_3428_, 3, v___x_3424_);
    lean_ctor_set_usize(v___x_3428_, 4, v___x_3423_);
    return v___x_3428_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__14()
-> *mut LeanObject {
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    v___x_3429_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__1);
    v___x_3430_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_3430_, 0, v___x_3429_);
    lean_ctor_set(v___x_3430_, 1, v___x_3429_);
    lean_ctor_set(v___x_3430_, 2, v___x_3429_);
    lean_ctor_set(v___x_3430_, 3, v___x_3429_);
    lean_ctor_set(v___x_3430_, 4, v___x_3429_);
    return v___x_3430_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__15()
-> *mut LeanObject {
    let mut v___x_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    v___x_3431_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__14_once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__14);
    v___x_3432_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__13_once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__13);
    v___x_3433_ = lean_box(1);
    v___x_3434_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__11_once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__11);
    v___x_3435_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0_spec__0___closed__2);
    v___x_3436_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_3436_, 0, v___x_3435_);
    lean_ctor_set(v___x_3436_, 1, v___x_3434_);
    lean_ctor_set(v___x_3436_, 2, v___x_3433_);
    lean_ctor_set(v___x_3436_, 3, v___x_3432_);
    lean_ctor_set(v___x_3436_, 4, v___x_3431_);
    return v___x_3436_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__20()
-> *mut LeanObject {
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    v___x_3444_ =
        l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__9;
    v___x_3445_ =
        l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__19;
    v___x_3446_ = l_Lean_mkConst(v___x_3445_, v___x_3444_);
    return v___x_3446_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__21()
-> *mut LeanObject {
    let mut v_type_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nil_3449_: *mut LeanObject = core::ptr::null_mut();
    v_type_3447_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5_once
        ),
        _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5,
    );
    v___x_3448_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__20), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__20_once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__20);
    v_nil_3449_ = l_Lean_Expr_app___override(v___x_3448_, v_type_3447_);
    return v_nil_3449_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__24()
-> *mut LeanObject {
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
    v___x_3454_ =
        l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__9;
    v___x_3455_ =
        l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__23;
    v___x_3456_ = l_Lean_mkConst(v___x_3455_, v___x_3454_);
    return v___x_3456_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__25()
-> *mut LeanObject {
    let mut v_type_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cons_3459_: *mut LeanObject = core::ptr::null_mut();
    v_type_3457_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5_once
        ),
        _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5,
    );
    v___x_3458_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__24), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__24_once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__24);
    v_cons_3459_ = l_Lean_Expr_app___override(v___x_3458_, v_type_3457_);
    return v_cons_3459_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin(
    mut v_declName_3460_: *mut LeanObject,
    mut v_args_3461_: *mut LeanObject,
    mut v_a_3462_: *mut LeanObject,
    mut v_a_3463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nil_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cons_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3490_: u8 = 0;
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3495_: u8 = 0;
    let mut v_a_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3499_: u8 = 0;
    let mut v___x_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3503_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3465_ = lean_box(0);
                v___x_3466_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__2_once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__2);
                v_type_3467_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5_once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__5);
                v___x_3468_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__10_once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__10);
                v___x_3469_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__15_once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__15);
                v___x_3470_ = lean_st_mk_ref(v___x_3469_);
                lean_inc(v_declName_3460_);
                v___x_3471_ = l_Lean_mkConst(v_declName_3460_, v___x_3465_);
                v___x_3472_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__17;
                v___x_3473_ = l_Lean_Name_append(v_declName_3460_, v___x_3472_);
                v___x_3474_ = l_Lean_Core_mkFreshUserName(v___x_3473_, v_a_3462_, v_a_3463_);
                if lean_obj_tag(v___x_3474_) == 0 {
                    v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
                    lean_inc(v_a_3475_);
                    lean_dec_ref_known(v___x_3474_, 1);
                    v_nil_3476_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__21), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__21_once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__21);
                    v_cons_3477_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__25), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__25_once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin___closed__25);
                    v___x_3478_ = lean_array_to_list(v_args_3461_);
                    v___x_3479_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin_spec__0(v_nil_3476_, v_cons_3477_, v___x_3478_);
                    v___x_3480_ = l_Lean_mkAppB(v___x_3468_, v_type_3467_, v___x_3479_);
                    v___x_3481_ = lean_unsigned_to_nat(2);
                    v___x_3482_ = lean_mk_empty_array_with_capacity(v___x_3481_);
                    v___x_3483_ = lean_array_push(v___x_3482_, v___x_3480_);
                    v___x_3484_ = lean_array_push(v___x_3483_, v___x_3471_);
                    v_val_3485_ = l_Lean_mkAppN(v___x_3466_, v___x_3484_);
                    lean_dec_ref(v___x_3484_);
                    v___x_3486_ =
                        l_Lean_declareBuiltin(v_a_3475_, v_val_3485_, v_a_3462_, v_a_3463_);
                    if lean_obj_tag(v___x_3486_) == 0 {
                        v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
                        v_isSharedCheck_3495_ = (!lean_is_exclusive(v___x_3486_)) as u8;
                        if v_isSharedCheck_3495_ == 0 {
                            v___x_3489_ = v___x_3486_;
                            v_isShared_3490_ = v_isSharedCheck_3495_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3487_);
                            lean_dec(v___x_3486_);
                            v___x_3489_ = lean_box(0);
                            v_isShared_3490_ = v_isSharedCheck_3495_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_3470_);
                        return v___x_3486_;
                    }
                } else {
                    lean_dec_ref(v___x_3471_);
                    lean_dec(v___x_3470_);
                    lean_dec_ref(v_args_3461_);
                    v_a_3496_ = lean_ctor_get(v___x_3474_, 0);
                    v_isSharedCheck_3503_ = (!lean_is_exclusive(v___x_3474_)) as u8;
                    if v_isSharedCheck_3503_ == 0 {
                        v___x_3498_ = v___x_3474_;
                        v_isShared_3499_ = v_isSharedCheck_3503_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3496_);
                        lean_dec(v___x_3474_);
                        v___x_3498_ = lean_box(0);
                        v_isShared_3499_ = v_isSharedCheck_3503_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3491_ = lean_st_ref_get(v___x_3470_);
                lean_dec(v___x_3470_);
                lean_dec(v___x_3491_);
                if v_isShared_3490_ == 0 {
                    v___x_3493_ = v___x_3489_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_a_3487_);
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
                    v_reuseFailAlloc_3502_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_a_3496_);
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
    mut v_declName_3504_: *mut LeanObject,
    mut v_args_3505_: *mut LeanObject,
    mut v_a_3506_: *mut LeanObject,
    mut v_a_3507_: *mut LeanObject,
    mut v_a_3508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3509_: *mut LeanObject = core::ptr::null_mut();
    v_res_3509_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin(
        v_declName_3504_,
        v_args_3505_,
        v_a_3506_,
        v_a_3507_,
    );
    lean_dec(v_a_3507_);
    lean_dec_ref(v_a_3506_);
    return v_res_3509_;
}
pub unsafe fn _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    v___x_3511_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_;
    v___x_3512_ = l_Lean_stringToMessageData(v___x_3511_);
    return v___x_3512_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_(
    mut v___x_3513_: *mut LeanObject,
    mut v___x_3514_: *mut LeanObject,
    mut v_decl_3515_: *mut LeanObject,
    mut v_stx_3516_: *mut LeanObject,
    mut v_kind_3517_: u8,
    mut v___y_3518_: *mut LeanObject,
    mut v___y_3519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: u8 = 0;
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3529_: usize = 0;
    let mut v___x_3530_: usize = 0;
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3535_: u8 = 0;
    let mut v___x_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3545_: u8 = 0;
    let mut v_a_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3549_: u8 = 0;
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3553_: u8 = 0;
    let mut v___x_3554_: u8 = 0;
    let mut v___x_3555_: u8 = 0;
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3554_ = 0;
                v___x_3555_ = l_Lean_instBEqAttributeKind_beq(v_kind_3517_, v___x_3554_);
                if v___x_3555_ == 0 {
                    lean_dec(v_stx_3516_);
                    lean_dec(v_decl_3515_);
                    lean_dec_ref(v___x_3514_);
                    lean_dec_ref(v___x_3513_);
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
                lean_inc(v_stx_3516_);
                v___x_3523_ = l_Lean_Syntax_isOfKind(v_stx_3516_, v___x_3522_);
                lean_dec(v___x_3522_);
                if v___x_3523_ == 0 {
                    lean_dec(v_stx_3516_);
                    lean_dec(v_decl_3515_);
                    v___x_3524_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2__once), _init_l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0___closed__1_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_);
                    v___x_3525_ = l_Lean_throwError___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2__spec__0___redArg(v___x_3524_, v___y_3518_, v___y_3519_);
                    return v___x_3525_;
                } else {
                    v___x_3526_ = lean_unsigned_to_nat(1);
                    v___x_3527_ = l_Lean_Syntax_getArg(v_stx_3516_, v___x_3526_);
                    lean_dec(v_stx_3516_);
                    v_args_3528_ = l_Lean_Syntax_getArgs(v___x_3527_);
                    lean_dec(v___x_3527_);
                    v_sz_3529_ = lean_array_size(v_args_3528_);
                    v___x_3530_ = 0usize;
                    v___x_3531_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2__spec__0(v_sz_3529_, v___x_3530_, v_args_3528_, v___y_3518_, v___y_3519_);
                    if lean_obj_tag(v___x_3531_) == 0 {
                        v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
                        v_isSharedCheck_3545_ = (!lean_is_exclusive(v___x_3531_)) as u8;
                        if v_isSharedCheck_3545_ == 0 {
                            v___x_3534_ = v___x_3531_;
                            v_isShared_3535_ = v_isSharedCheck_3545_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_3532_);
                            lean_dec(v___x_3531_);
                            v___x_3534_ = lean_box(0);
                            v_isShared_3535_ = v_isSharedCheck_3545_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_decl_3515_);
                        v_a_3546_ = lean_ctor_get(v___x_3531_, 0);
                        v_isSharedCheck_3553_ = (!lean_is_exclusive(v___x_3531_)) as u8;
                        if v_isSharedCheck_3553_ == 0 {
                            v___x_3548_ = v___x_3531_;
                            v_isShared_3549_ = v_isSharedCheck_3553_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3546_);
                            lean_dec(v___x_3531_);
                            v___x_3548_ = lean_box(0);
                            v_isShared_3549_ = v_isSharedCheck_3553_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_3536_ = lean_st_ref_get(v___y_3519_);
                v_env_3537_ = lean_ctor_get(v___x_3536_, 0);
                lean_inc_ref(v_env_3537_);
                lean_dec(v___x_3536_);
                lean_inc(v_decl_3515_);
                v___x_3538_ = lean_decl_get_sorry_dep(v_env_3537_, v_decl_3515_);
                if lean_obj_tag(v___x_3538_) == 0 {
                    lean_del_object(v___x_3534_);
                    v___x_3539_ =
                        l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin(
                            v_decl_3515_,
                            v_a_3532_,
                            v___y_3518_,
                            v___y_3519_,
                        );
                    return v___x_3539_;
                } else {
                    lean_dec_ref_known(v___x_3538_, 1);
                    if v___x_3523_ == 0 {
                        lean_del_object(v___x_3534_);
                        v___x_3540_ =
                            l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_addBuiltin(
                                v_decl_3515_,
                                v_a_3532_,
                                v___y_3518_,
                                v___y_3519_,
                            );
                        return v___x_3540_;
                    } else {
                        lean_dec(v_a_3532_);
                        lean_dec(v_decl_3515_);
                        v___x_3541_ = lean_box(0);
                        if v_isShared_3535_ == 0 {
                            lean_ctor_set(v___x_3534_, 0, v___x_3541_);
                            v___x_3543_ = v___x_3534_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3544_, 0, v___x_3541_);
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
                    v_reuseFailAlloc_3552_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_a_3546_);
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
    mut v___x_3558_: *mut LeanObject,
    mut v___x_3559_: *mut LeanObject,
    mut v_decl_3560_: *mut LeanObject,
    mut v_stx_3561_: *mut LeanObject,
    mut v_kind_3562_: *mut LeanObject,
    mut v___y_3563_: *mut LeanObject,
    mut v___y_3564_: *mut LeanObject,
    mut v___y_3565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_3566_: u8 = 0;
    let mut v_res_3567_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_3566_ = (lean_unbox(v_kind_3562_) as u8);
    v_res_3567_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___lam__0_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_(v___x_3558_, v___x_3559_, v_decl_3560_, v_stx_3561_, v_kind_boxed_3566_, v___y_3563_, v___y_3564_);
    lean_dec(v___y_3564_);
    lean_dec_ref(v___y_3563_);
    return v_res_3567_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    v___x_3599_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn___closed__10_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_;
    v___x_3600_ = l_Lean_registerBuiltinAttribute(v___x_3599_);
    return v___x_3600_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2____boxed(
    mut v_a_3601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3602_: *mut LeanObject = core::ptr::null_mut();
    v_res_3602_ = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_();
    return v_res_3602_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_CodeActions_Attr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Server_CodeActions_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_73882864____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_CodeAction_holeCodeActionExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_CodeAction_holeCodeActionExt);
    lean_dec_ref(res);
    res = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1824323934____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_262607364____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_CodeAction_builtinCmdCodeActions = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_CodeAction_builtinCmdCodeActions);
    lean_dec_ref(res);
    res = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_145477870____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_CodeAction_cmdCodeActionExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_CodeAction_cmdCodeActionExt);
    lean_dec_ref(res);
    res = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_249496773____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Server_CodeActions_Attr_0__Lean_CodeAction_initFn_00___x40_Lean_Server_CodeActions_Attr_1324802641____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_CodeActions_Attr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Server_CodeActions_Attr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Server_CodeActions_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_IR_CompilerM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_CodeActions_Attr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Server_CodeActions_Attr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Server_CodeActions_Attr(builtin);
}
