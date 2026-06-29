// Lean compiler output
// Module: Lean.Linter.Extra.UnusedDecidableInType
// Imports: Lean.Linter.Basic Lean.Meta.ForEachExpr Lean.Meta.Sorry Lean.PrivateName Lean.Server.InfoUtils Lean.Linter.Util
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_mkStr5, l_Lean_Name_mkStr6,
    l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_replaceRef,
};
use crate::r#gen::Init::System::ST::{l_ST_Prim_Ref_get___boxed, l_ST_Prim_mkRef___boxed};
use crate::r#gen::Lean::Data::Name::{
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl, l_Lean_Name_isPrefixOf,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    l_Lean_Elab_Command_addLinter, l_Lean_Elab_Command_liftTermElabM___redArg,
};
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Environment::{
    l_Lean_AsyncConstantInfo_toConstantVal, l_Lean_Environment_findAsync_x3f,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_BinderInfo_isInstImplicit, l_Lean_Expr_binderInfo, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_fvarId_x21, l_Lean_Expr_getAppFn_x27, l_Lean_Expr_hasFVar, l_Lean_Expr_hash,
    l_Lean_Expr_isForall, l_Lean_FVarIdSet_insert, l_Lean_instInhabitedExpr,
};
use crate::r#gen::Lean::Linter::Basic::{
    initialize_Lean_Linter_Basic, l_Lean_withSetOptionIn___boxed,
    runtime_initialize_Lean_Linter_Basic,
};
use crate::r#gen::Lean::Linter::Init::{
    l_Lean_Linter_getLinterValueExtra, l_Lean_Linter_linterMessageTag, l_Lean_Linter_linterSetsExt,
};
use crate::r#gen::Lean::Linter::Util::{
    initialize_Lean_Linter_Util, l_Lean_Linter_getDeclsByBody, runtime_initialize_Lean_Linter_Util,
};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_nil,
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_MessageLog_add,
    l_Lean_MessageLog_hasErrors, l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp,
};
use crate::r#gen::Lean::Meta::ForEachExpr::{
    initialize_Lean_Meta_ForEachExpr, runtime_initialize_Lean_Meta_ForEachExpr,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProof;
use crate::r#gen::Lean::Meta::Sorry::{
    initialize_Lean_Meta_Sorry, l_Lean_Meta_mkSorry, runtime_initialize_Lean_Meta_Sorry,
};
use crate::r#gen::Lean::PrivateName::{
    initialize_Lean_PrivateName, l_Lean_privateToUserName, runtime_initialize_Lean_PrivateName,
};
use crate::r#gen::Lean::Server::InfoUtils::{
    initialize_Lean_Server_InfoUtils, runtime_initialize_Lean_Server_InfoUtils,
};
use crate::r#gen::Lean::Util::Sorry::{l_Lean_Expr_hasSorry, l_Lean_Expr_isSorry};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_nat_sub, lean_string_dec_eq, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::{
    lean_expr_eqv, lean_expr_has_loose_bvar, lean_expr_instantiate_rev, lean_expr_instantiate1,
};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [101, 120, 116, 114, 97, 0]};
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [117, 110, 117, 115, 101, 100, 68, 101, 99, 105, 100, 97, 98, 108, 101, 73, 110, 84, 121, 112, 101, 0]};
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5701751079888345786 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,8383467597245298465 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,9766370603958561406 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<221> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 221, m_capacity: 221, m_length: 220, m_data: [101, 110, 97, 98, 108, 101, 32, 116, 104, 101, 32, 117, 110, 117, 115, 101, 100, 32, 96, 68, 101, 99, 105, 100, 97, 98, 108, 101, 42, 96, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 108, 105, 110, 116, 101, 114, 44, 32, 119, 104, 105, 99, 104, 32, 108, 105, 110, 116, 115, 32, 97, 103, 97, 105, 110, 115, 116, 32, 96, 68, 101, 99, 105, 100, 97, 98, 108, 101, 42, 96, 32, 105, 110, 115, 116, 97, 110, 99, 101, 115, 32, 105, 110, 32, 116, 104, 101, 32, 104, 121, 112, 111, 116, 104, 101, 115, 101, 115, 32, 111, 102, 32, 116, 104, 101, 111, 114, 101, 109, 115, 32, 119, 104, 105, 99, 104, 32, 97, 114, 101, 32, 110, 111, 116, 32, 117, 115, 101, 100, 32, 105, 110, 32, 116, 104, 101, 32, 116, 121, 112, 101, 44, 32, 97, 110, 100, 32, 99, 97, 110, 32, 116, 104, 101, 114, 101, 102, 111, 114, 101, 32, 98, 101, 32, 114, 101, 112, 108, 97, 99, 101, 100, 32, 98, 121, 32, 97, 32, 117, 115, 101, 32, 111, 102, 32, 96, 99, 108, 97, 115, 115, 105, 99, 97, 108, 96, 32, 105, 110, 32, 116, 104, 101, 32, 112, 114, 111, 111, 102, 46, 0]};
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__4_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [76, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [69, 120, 116, 114, 97, 0]};
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,8071394701935581384 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,14342914028213736627 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__0_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,8412578185445384546 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__1_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,9890441027862740329 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__2_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11385213656783527526 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Linter_Extra_linter_extra_unusedDecidableInType:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__0_value: crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [32, 40, 117, 115, 101, 100, 32, 105, 110, 32, 116, 121, 112, 101, 44, 32, 98, 117, 116, 32, 111, 110, 108, 121, 32, 105, 110, 32, 97, 32, 112, 114, 111, 111, 102, 41, 0]};
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [93, 32, 40, 35, 0]};
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__6_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__8_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 35, 0]};
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 5, m_data: [10, 32, 32, 226, 128, 162, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__2_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [32, 105, 110, 32, 105, 116, 115, 32, 116, 121, 112, 101, 0]};
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__4_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__5_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [32, 111, 117, 116, 115, 105, 100, 101, 32, 111, 102, 32, 112, 114, 111, 111, 102, 115, 0]};
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__6_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__8_value: crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [96, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 117, 115, 101, 32, 116, 104, 101, 32, 102, 111, 108, 108, 111, 119, 105, 110, 103, 32, 0]};
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__10_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [104, 121, 112, 111, 116, 104, 101, 115, 101, 115, 0]};
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__11_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [104, 121, 112, 111, 116, 104, 101, 115, 105, 115, 0]};
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__0_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [68, 101, 99, 105, 100, 97, 98, 108, 101, 82, 101, 108, 0]};
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,3727702598694774143 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__2_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [68, 101, 99, 105, 100, 97, 98, 108, 101, 69, 113, 0]};
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__2_value) as *mut crate::leanh::LeanObject,18231208422245114676 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__4_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [68, 101, 99, 105, 100, 97, 98, 108, 101, 76, 69, 0]};
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__4_value) as *mut crate::leanh::LeanObject,9792299347440354849 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__6_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [68, 101, 99, 105, 100, 97, 98, 108, 101, 76, 84, 0]};
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__6_value) as *mut crate::leanh::LeanObject,17168815159481401969 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__8_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [68, 101, 99, 105, 100, 97, 98, 108, 101, 0]};
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__8_value) as *mut crate::leanh::LeanObject,4342836574150310743 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__10_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [68, 101, 99, 105, 100, 97, 98, 108, 101, 80, 114, 101, 100, 0]};
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__10_value) as *mut crate::leanh::LeanObject,11369803451403856912 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__3_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__5_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__6_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5___closed__0_value: crate::leanh::LeanStringObject<46> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [84, 104, 105, 115, 32, 108, 105, 110, 116, 101, 114, 32, 99, 97, 110, 32, 98, 101, 32, 100, 105, 115, 97, 98, 108, 101, 100, 32, 119, 105, 116, 104, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 0]};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5___closed__2_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [32, 102, 97, 108, 115, 101, 96, 0]};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [10, 10, 67, 111, 110, 115, 105, 100, 101, 114, 32, 114, 101, 109, 111, 118, 105, 110, 103, 32, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__2_value: crate::leanh::LeanStringObject<141> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 141, m_capacity: 141, m_length: 140, m_data: [32, 97, 110, 100, 32, 117, 115, 105, 110, 103, 32, 96, 99, 108, 97, 115, 115, 105, 99, 97, 108, 96, 32, 105, 110, 32, 116, 104, 101, 32, 112, 114, 111, 111, 102, 32, 105, 110, 115, 116, 101, 97, 100, 46, 32, 70, 111, 114, 32, 116, 101, 114, 109, 115, 44, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 117, 115, 105, 110, 103, 32, 96, 111, 112, 101, 110, 32, 115, 99, 111, 112, 101, 100, 32, 67, 108, 97, 115, 115, 105, 99, 97, 108, 32, 105, 110, 96, 32, 97, 116, 32, 116, 104, 101, 32, 116, 101, 114, 109, 32, 108, 101, 118, 101, 108, 32, 40, 110, 111, 116, 32, 116, 104, 101, 32, 99, 111, 109, 109, 97, 110, 100, 32, 108, 101, 118, 101, 108, 41, 46, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__4_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [116, 104, 101, 115, 101, 32, 104, 121, 112, 111, 116, 104, 101, 115, 101, 115, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__5_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [116, 104, 105, 115, 32, 104, 121, 112, 111, 116, 104, 101, 115, 105, 115, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___lam__0___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__1_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_Lean_withSetOptionIn___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__2_value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [85, 110, 117, 115, 101, 100, 68, 101, 99, 105, 100, 97, 98, 108, 101, 73, 110, 84, 121, 112, 101, 0]};
static mut l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__3_value: crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [117, 110, 117, 115, 101, 100, 68, 101, 99, 105, 100, 97, 98, 108, 101, 73, 110, 84, 121, 112, 101, 76, 105, 110, 116, 101, 114, 0]};
static mut l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__3_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__6_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__7_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,8071394701935581384 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__8_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,14342914028213736627 as *mut crate::leanh::LeanObject] };
static l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__4_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__2_value) as *mut crate::leanh::LeanObject,13906403133224464093 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__4_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__3_value) as *mut crate::leanh::LeanObject,8250198919425597394 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__5_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__1_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___closed__5_value
) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_isAppOrForallOfConstP(
    mut v_p_3009_: *mut crate::leanh::LeanObject,
    mut v_type_3010_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: u8 = 0;
    let mut v_body_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3011_ = l_Lean_Expr_cleanupAnnotations(v_type_3010_);
                v___x_3012_ = l_Lean_Expr_getAppFn_x27(v___x_3011_);
                crate::leanh::lean_dec_ref(v___x_3011_);
                match crate::leanh::lean_obj_tag(v___x_3012_) {
                    4 => {
                        v_declName_3013_ = crate::leanh::lean_ctor_get(v___x_3012_, 0);
                        crate::leanh::lean_inc(v_declName_3013_);
                        crate::leanh::lean_dec_ref_known(v___x_3012_, 2);
                        v___x_3014_ = crate::leanh::lean_apply_1(v_p_3009_, v_declName_3013_);
                        v___x_3015_ = (crate::leanh::lean_unbox(v___x_3014_) as u8);
                        return v___x_3015_;
                    }
                    7 => {
                        v_body_3016_ = crate::leanh::lean_ctor_get(v___x_3012_, 2);
                        crate::leanh::lean_inc_ref(v_body_3016_);
                        crate::leanh::lean_dec_ref_known(v___x_3012_, 3);
                        v_type_3010_ = v_body_3016_;
                        state = 0;
                        continue;
                    }
                    _ => {
                        crate::leanh::lean_dec_ref(v___x_3012_);
                        crate::leanh::lean_dec_ref(v_p_3009_);
                        v___x_3018_ = 0;
                        return v___x_3018_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_isAppOrForallOfConstP___boxed(
    mut v_p_3019_: *mut crate::leanh::LeanObject,
    mut v_type_3020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3021_: u8 = 0;
    let mut v_r_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3021_ =
        l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_isAppOrForallOfConstP(
            v_p_3019_,
            v_type_3020_,
        );
    v_r_3022_ = crate::leanh::lean_box((v_res_3021_) as usize);
    return v_r_3022_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_hasInstanceBinderOf(
    mut v_p_3023_: *mut crate::leanh::LeanObject,
    mut v_e_3024_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3028_: u8 = 0;
    let mut v___y_3030_: u8 = 0;
    let mut v___x_3032_: u8 = 0;
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: u8 = 0;
    let mut v_body_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3025_ = l_Lean_Expr_cleanupAnnotations(v_e_3024_);
                match crate::leanh::lean_obj_tag(v___x_3025_) {
                    7 => {
                        v_binderType_3026_ = crate::leanh::lean_ctor_get(v___x_3025_, 1);
                        crate::leanh::lean_inc_ref(v_binderType_3026_);
                        v_body_3027_ = crate::leanh::lean_ctor_get(v___x_3025_, 2);
                        crate::leanh::lean_inc_ref(v_body_3027_);
                        v_binderInfo_3028_ = crate::leanh::lean_ctor_get_uint8(
                            v___x_3025_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        );
                        crate::leanh::lean_dec_ref_known(v___x_3025_, 3);
                        v___x_3032_ = l_Lean_BinderInfo_isInstImplicit(v_binderInfo_3028_);
                        if v___x_3032_ == 0 {
                            crate::leanh::lean_dec_ref(v_binderType_3026_);
                            v___y_3030_ = v___x_3032_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc_ref(v_p_3023_);
                            v___x_3033_ = crate::leanh::lean_apply_1(v_p_3023_, v_binderType_3026_);
                            v___x_3034_ = (crate::leanh::lean_unbox(v___x_3033_) as u8);
                            v___y_3030_ = v___x_3034_;
                            state = 1;
                            continue;
                        }
                    }
                    8 => {
                        v_body_3035_ = crate::leanh::lean_ctor_get(v___x_3025_, 3);
                        crate::leanh::lean_inc_ref(v_body_3035_);
                        crate::leanh::lean_dec_ref_known(v___x_3025_, 4);
                        v_e_3024_ = v_body_3035_;
                        state = 0;
                        continue;
                    }
                    _ => {
                        crate::leanh::lean_dec_ref(v___x_3025_);
                        crate::leanh::lean_dec_ref(v_p_3023_);
                        v___x_3037_ = 0;
                        return v___x_3037_;
                    }
                }
            }
            1 => {
                if v___y_3030_ == 0 {
                    v_e_3024_ = v_body_3027_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_body_3027_);
                    crate::leanh::lean_dec_ref(v_p_3023_);
                    return v___y_3030_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_hasInstanceBinderOf___boxed(
    mut v_p_3038_: *mut crate::leanh::LeanObject,
    mut v_e_3039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3040_: u8 = 0;
    let mut v_r_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3040_ =
        l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_hasInstanceBinderOf(
            v_p_3038_, v_e_3039_,
        );
    v_r_3041_ = crate::leanh::lean_box((v_res_3040_) as usize);
    return v_r_3041_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere_go(
    mut v_p_3042_: *mut crate::leanh::LeanObject,
    mut v_body_3043_: *mut crate::leanh::LeanObject,
    mut v_current_3044_: *mut crate::leanh::LeanObject,
    mut v_acc_3045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3049_: u8 = 0;
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3053_: u8 = 0;
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: u8 = 0;
    let mut v___x_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: u8 = 0;
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: u8 = 0;
    let mut v_body_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3046_ = l_Lean_Expr_cleanupAnnotations(v_body_3043_);
                match crate::leanh::lean_obj_tag(v___x_3046_) {
                    7 => {
                        v_binderType_3047_ = crate::leanh::lean_ctor_get(v___x_3046_, 1);
                        crate::leanh::lean_inc_ref(v_binderType_3047_);
                        v_body_3048_ = crate::leanh::lean_ctor_get(v___x_3046_, 2);
                        crate::leanh::lean_inc_ref(v_body_3048_);
                        v_binderInfo_3049_ = crate::leanh::lean_ctor_get_uint8(
                            v___x_3046_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        );
                        crate::leanh::lean_dec_ref_known(v___x_3046_, 3);
                        v___x_3050_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3051_ = lean_nat_add(v_current_3044_, v___x_3050_);
                        v___x_3060_ = l_Lean_BinderInfo_isInstImplicit(v_binderInfo_3049_);
                        if v___x_3060_ == 0 {
                            crate::leanh::lean_dec_ref(v_binderType_3047_);
                            v___y_3053_ = v___x_3060_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc_ref(v_p_3042_);
                            v___x_3061_ = crate::leanh::lean_apply_1(v_p_3042_, v_binderType_3047_);
                            v___x_3062_ = (crate::leanh::lean_unbox(v___x_3061_) as u8);
                            v___y_3053_ = v___x_3062_;
                            state = 1;
                            continue;
                        }
                    }
                    8 => {
                        v_body_3063_ = crate::leanh::lean_ctor_get(v___x_3046_, 3);
                        crate::leanh::lean_inc_ref(v_body_3063_);
                        crate::leanh::lean_dec_ref_known(v___x_3046_, 4);
                        v_body_3043_ = v_body_3063_;
                        state = 0;
                        continue;
                    }
                    _ => {
                        crate::leanh::lean_dec_ref(v___x_3046_);
                        crate::leanh::lean_dec(v_current_3044_);
                        crate::leanh::lean_dec_ref(v_p_3042_);
                        return v_acc_3045_;
                    }
                }
            }
            1 => {
                if v___y_3053_ == 0 {
                    crate::leanh::lean_dec(v_current_3044_);
                    v_body_3043_ = v_body_3048_;
                    v_current_3044_ = v___x_3051_;
                    state = 0;
                    continue;
                } else {
                    v___x_3055_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3056_ = lean_expr_has_loose_bvar(v_body_3048_, v___x_3055_);
                    if v___x_3056_ == 0 {
                        v___x_3057_ = lean_array_push(v_acc_3045_, v_current_3044_);
                        v_body_3043_ = v_body_3048_;
                        v_current_3044_ = v___x_3051_;
                        v_acc_3045_ = v___x_3057_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_current_3044_);
                        v_body_3043_ = v_body_3048_;
                        v_current_3044_ = v___x_3051_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere(
    mut v_p_3067_: *mut crate::leanh::LeanObject,
    mut v_e_3068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3069_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3070_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere___closed__0;
    v___x_3071_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere_go(v_p_3067_, v_e_3068_, v___x_3069_, v___x_3070_);
    return v___x_3071_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findConstValOfKind_x3f(
    mut v_env_3072_: *mut crate::leanh::LeanObject,
    mut v_p_3073_: *mut crate::leanh::LeanObject,
    mut v_decl_3074_: *mut crate::leanh::LeanObject,
    mut v_skipRealize_3075_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3081_: u8 = 0;
    let mut v_kind_3082_: u8 = 0;
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: u8 = 0;
    let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3091_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3076_ = l_Lean_Environment_findAsync_x3f(
                    v_env_3072_,
                    v_decl_3074_,
                    v_skipRealize_3075_,
                );
                if crate::leanh::lean_obj_tag(v___x_3076_) == 0 {
                    crate::leanh::lean_dec_ref(v_p_3073_);
                    v___x_3077_ = crate::leanh::lean_box(0);
                    return v___x_3077_;
                } else {
                    v_val_3078_ = crate::leanh::lean_ctor_get(v___x_3076_, 0);
                    v_isSharedCheck_3091_ = (!crate::leanh::lean_is_exclusive(v___x_3076_)) as u8;
                    if v_isSharedCheck_3091_ == 0 {
                        v___x_3080_ = v___x_3076_;
                        v_isShared_3081_ = v_isSharedCheck_3091_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3078_);
                        crate::leanh::lean_dec(v___x_3076_);
                        v___x_3080_ = crate::leanh::lean_box(0);
                        v_isShared_3081_ = v_isSharedCheck_3091_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_kind_3082_ = crate::leanh::lean_ctor_get_uint8(
                    v_val_3078_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v___x_3083_ = crate::leanh::lean_box((v_kind_3082_) as usize);
                v___x_3084_ = crate::leanh::lean_apply_1(v_p_3073_, v___x_3083_);
                v___x_3085_ = (crate::leanh::lean_unbox(v___x_3084_) as u8);
                if v___x_3085_ == 0 {
                    crate::leanh::lean_del_object(v___x_3080_);
                    crate::leanh::lean_dec(v_val_3078_);
                    v___x_3086_ = crate::leanh::lean_box(0);
                    return v___x_3086_;
                } else {
                    v___x_3087_ = l_Lean_AsyncConstantInfo_toConstantVal(v_val_3078_);
                    if v_isShared_3081_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3080_, 0, v___x_3087_);
                        v___x_3089_ = v___x_3080_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3090_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3090_, 0, v___x_3087_);
                        v___x_3089_ = v_reuseFailAlloc_3090_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3089_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findConstValOfKind_x3f___boxed(
    mut v_env_3092_: *mut crate::leanh::LeanObject,
    mut v_p_3093_: *mut crate::leanh::LeanObject,
    mut v_decl_3094_: *mut crate::leanh::LeanObject,
    mut v_skipRealize_3095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipRealize_boxed_3096_: u8 = 0;
    let mut v_res_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_3096_ = (crate::leanh::lean_unbox(v_skipRealize_3095_) as u8);
    v_res_3097_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findConstValOfKind_x3f(v_env_3092_, v_p_3093_, v_decl_3094_, v_skipRealize_boxed_3096_);
    return v_res_3097_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___lam__0(
    mut v_x_3098_: u8,
) -> u8 {
    if v_x_3098_ == 1 {
        let mut v___x_3099_: u8 = 0;
        v___x_3099_ = 1;
        return v___x_3099_;
    } else {
        let mut v___x_3100_: u8 = 0;
        v___x_3100_ = 0;
        return v___x_3100_;
    }
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___lam__0___boxed(
    mut v_x_3101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_26__boxed_3102_: u8 = 0;
    let mut v_res_3103_: u8 = 0;
    let mut v_r_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_3102_ = (crate::leanh::lean_unbox(v_x_3101_) as u8);
    v_res_3103_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___lam__0(v_x_26__boxed_3102_);
    v_r_3104_ = crate::leanh::lean_box((v_res_3103_) as usize);
    return v_r_3104_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f(
    mut v_env_3106_: *mut crate::leanh::LeanObject,
    mut v_decl_3107_: *mut crate::leanh::LeanObject,
    mut v_skipRealize_3108_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3109_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___closed__0;
    v___x_3110_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findConstValOfKind_x3f(v_env_3106_, v___f_3109_, v_decl_3107_, v_skipRealize_3108_);
    return v___x_3110_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f___boxed(
    mut v_env_3111_: *mut crate::leanh::LeanObject,
    mut v_decl_3112_: *mut crate::leanh::LeanObject,
    mut v_skipRealize_3113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipRealize_boxed_3114_: u8 = 0;
    let mut v_res_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_3114_ = (crate::leanh::lean_unbox(v_skipRealize_3113_) as u8);
    v_res_3115_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f(v_env_3111_, v_decl_3112_, v_skipRealize_boxed_3114_);
    return v_res_3115_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__spec__0(
    mut v_name_3116_: *mut crate::leanh::LeanObject,
    mut v_decl_3117_: *mut crate::leanh::LeanObject,
    mut v_ref_3118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: u8 = 0;
    let mut v___x_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3129_: u8 = 0;
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3134_: u8 = 0;
    let mut v_unused_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3139_: u8 = 0;
    let mut v___x_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3143_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_3120_ = crate::leanh::lean_ctor_get(v_decl_3117_, 0);
                v_descr_3121_ = crate::leanh::lean_ctor_get(v_decl_3117_, 1);
                v_deprecation_x3f_3122_ = crate::leanh::lean_ctor_get(v_decl_3117_, 2);
                v___x_3123_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_3124_ = (crate::leanh::lean_unbox(v_defValue_3120_) as u8);
                crate::leanh::lean_ctor_set_uint8(v___x_3123_, 0 as u32, v___x_3124_);
                crate::leanh::lean_inc(v_deprecation_x3f_3122_);
                crate::leanh::lean_inc_ref(v_descr_3121_);
                crate::leanh::lean_inc_n(v_name_3116_, 2);
                v___x_3125_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3125_, 0, v_name_3116_);
                crate::leanh::lean_ctor_set(v___x_3125_, 1, v_ref_3118_);
                crate::leanh::lean_ctor_set(v___x_3125_, 2, v___x_3123_);
                crate::leanh::lean_ctor_set(v___x_3125_, 3, v_descr_3121_);
                crate::leanh::lean_ctor_set(v___x_3125_, 4, v_deprecation_x3f_3122_);
                v___x_3126_ = lean_register_option(v_name_3116_, v___x_3125_);
                if crate::leanh::lean_obj_tag(v___x_3126_) == 0 {
                    v_isSharedCheck_3134_ = (!crate::leanh::lean_is_exclusive(v___x_3126_)) as u8;
                    if v_isSharedCheck_3134_ == 0 {
                        v_unused_3135_ = crate::leanh::lean_ctor_get(v___x_3126_, 0);
                        crate::leanh::lean_dec(v_unused_3135_);
                        v___x_3128_ = v___x_3126_;
                        v_isShared_3129_ = v_isSharedCheck_3134_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3126_);
                        v___x_3128_ = crate::leanh::lean_box(0);
                        v_isShared_3129_ = v_isSharedCheck_3134_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_3116_);
                    v_a_3136_ = crate::leanh::lean_ctor_get(v___x_3126_, 0);
                    v_isSharedCheck_3143_ = (!crate::leanh::lean_is_exclusive(v___x_3126_)) as u8;
                    if v_isSharedCheck_3143_ == 0 {
                        v___x_3138_ = v___x_3126_;
                        v_isShared_3139_ = v_isSharedCheck_3143_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3136_);
                        crate::leanh::lean_dec(v___x_3126_);
                        v___x_3138_ = crate::leanh::lean_box(0);
                        v_isShared_3139_ = v_isSharedCheck_3143_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_3120_);
                v___x_3130_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3130_, 0, v_name_3116_);
                crate::leanh::lean_ctor_set(v___x_3130_, 1, v_defValue_3120_);
                if v_isShared_3129_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3128_, 0, v___x_3130_);
                    v___x_3132_ = v___x_3128_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3133_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3133_, 0, v___x_3130_);
                    v___x_3132_ = v_reuseFailAlloc_3133_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3132_;
            }
            3 => {
                if v_isShared_3139_ == 0 {
                    v___x_3141_ = v___x_3138_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3142_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
                    v___x_3141_ = v_reuseFailAlloc_3142_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3141_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_3144_: *mut crate::leanh::LeanObject,
    mut v_decl_3145_: *mut crate::leanh::LeanObject,
    mut v_ref_3146_: *mut crate::leanh::LeanObject,
    mut v_a_3147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3148_ = l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__spec__0(v_name_3144_, v_decl_3145_, v_ref_3146_);
    crate::leanh::lean_dec_ref(v_decl_3145_);
    return v_res_3148_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3173_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__3_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_;
    v___x_3174_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__5_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_;
    v___x_3175_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn___closed__9_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_;
    v___x_3176_ = l_Lean_Option_register___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4__spec__0(v___x_3173_, v___x_3174_, v___x_3175_);
    return v___x_3176_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4____boxed(
    mut v_a_3177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3178_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_();
    return v_res_3178_;
}
pub unsafe fn _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3180_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__0;
    v___x_3181_ = l_Lean_stringToMessageData(v___x_3180_);
    return v___x_3181_;
}
pub unsafe fn _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3183_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__2;
    v___x_3184_ = l_Lean_stringToMessageData(v___x_3183_);
    return v___x_3184_;
}
pub unsafe fn _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3186_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__4;
    v___x_3187_ = l_Lean_stringToMessageData(v___x_3186_);
    return v___x_3187_;
}
pub unsafe fn _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3189_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__6;
    v___x_3190_ = l_Lean_stringToMessageData(v___x_3189_);
    return v___x_3190_;
}
pub unsafe fn _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3192_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__8;
    v___x_3193_ = l_Lean_stringToMessageData(v___x_3192_);
    return v___x_3193_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0(
    mut v_param_3194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_type_x3f_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_appearsInTypeProof_3197_: u8 = 0;
    let mut v___y_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3205_: u8 = 0;
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3221_: u8 = 0;
    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_type_x3f_3195_ = crate::leanh::lean_ctor_get(v_param_3194_, 1);
                crate::leanh::lean_inc(v_type_x3f_3195_);
                v_idx_3196_ = crate::leanh::lean_ctor_get(v_param_3194_, 2);
                crate::leanh::lean_inc(v_idx_3196_);
                v_appearsInTypeProof_3197_ = crate::leanh::lean_ctor_get_uint8(
                    v_param_3194_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec_ref(v_param_3194_);
                if crate::leanh::lean_obj_tag(v_type_x3f_3195_) == 1 {
                    v_val_3202_ = crate::leanh::lean_ctor_get(v_type_x3f_3195_, 0);
                    v_isSharedCheck_3221_ =
                        (!crate::leanh::lean_is_exclusive(v_type_x3f_3195_)) as u8;
                    if v_isSharedCheck_3221_ == 0 {
                        v___x_3204_ = v_type_x3f_3195_;
                        v_isShared_3205_ = v_isSharedCheck_3221_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3202_);
                        crate::leanh::lean_dec(v_type_x3f_3195_);
                        v___x_3204_ = crate::leanh::lean_box(0);
                        v_isShared_3205_ = v_isSharedCheck_3221_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_type_x3f_3195_);
                    v___x_3222_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9_once), _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9);
                    v___x_3223_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3224_ = lean_nat_add(v_idx_3196_, v___x_3223_);
                    crate::leanh::lean_dec(v_idx_3196_);
                    v___x_3225_ = l_Nat_reprFast(v___x_3224_);
                    v___x_3226_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3226_, 0, v___x_3225_);
                    v___x_3227_ = l_Lean_MessageData_ofFormat(v___x_3226_);
                    v___x_3228_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3228_, 0, v___x_3222_);
                    crate::leanh::lean_ctor_set(v___x_3228_, 1, v___x_3227_);
                    v___y_3199_ = v___x_3228_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_appearsInTypeProof_3197_ == 0 {
                    return v___y_3199_;
                } else {
                    v___x_3200_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1_once), _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1);
                    v_msg_3201_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_msg_3201_, 0, v___y_3199_);
                    crate::leanh::lean_ctor_set(v_msg_3201_, 1, v___x_3200_);
                    return v_msg_3201_;
                }
            }
            2 => {
                v___x_3206_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3_once), _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3);
                v___x_3207_ = l_Lean_MessageData_ofExpr(v_val_3202_);
                v___x_3208_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3208_, 0, v___x_3206_);
                crate::leanh::lean_ctor_set(v___x_3208_, 1, v___x_3207_);
                v___x_3209_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5_once), _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5);
                v___x_3210_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3210_, 0, v___x_3208_);
                crate::leanh::lean_ctor_set(v___x_3210_, 1, v___x_3209_);
                v___x_3211_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3212_ = lean_nat_add(v_idx_3196_, v___x_3211_);
                crate::leanh::lean_dec(v_idx_3196_);
                v___x_3213_ = l_Nat_reprFast(v___x_3212_);
                if v_isShared_3205_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3204_, 3);
                    crate::leanh::lean_ctor_set(v___x_3204_, 0, v___x_3213_);
                    v___x_3215_ = v___x_3204_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3220_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3220_, 0, v___x_3213_);
                    v___x_3215_ = v_reuseFailAlloc_3220_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3216_ = l_Lean_MessageData_ofFormat(v___x_3215_);
                v___x_3217_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3217_, 0, v___x_3210_);
                crate::leanh::lean_ctor_set(v___x_3217_, 1, v___x_3216_);
                v___x_3218_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7_once), _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7);
                v___x_3219_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3219_, 0, v___x_3217_);
                crate::leanh::lean_ctor_set(v___x_3219_, 1, v___x_3218_);
                v___y_3199_ = v___x_3219_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__2(
    mut v_as_3231_: *mut crate::leanh::LeanObject,
    mut v_i_3232_: usize,
    mut v_stop_3233_: usize,
    mut v_b_3234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3235_: u8 = 0;
    let mut v___x_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: usize = 0;
    let mut v___x_3239_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3235_ = lean_usize_dec_eq(v_i_3232_, v_stop_3233_);
                if v___x_3235_ == 0 {
                    v___x_3236_ = lean_array_uget_borrowed(v_as_3231_, v_i_3232_);
                    crate::leanh::lean_inc(v___x_3236_);
                    v___x_3237_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3237_, 0, v_b_3234_);
                    crate::leanh::lean_ctor_set(v___x_3237_, 1, v___x_3236_);
                    v___x_3238_ = 1usize;
                    v___x_3239_ = lean_usize_add(v_i_3232_, v___x_3238_);
                    v_i_3232_ = v___x_3239_;
                    v_b_3234_ = v___x_3237_;
                    state = 0;
                    continue;
                } else {
                    return v_b_3234_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__2___boxed(
    mut v_as_3241_: *mut crate::leanh::LeanObject,
    mut v_i_3242_: *mut crate::leanh::LeanObject,
    mut v_stop_3243_: *mut crate::leanh::LeanObject,
    mut v_b_3244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3245_: usize = 0;
    let mut v_stop_boxed_3246_: usize = 0;
    let mut v_res_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3245_ = crate::leanh::lean_unbox_usize(v_i_3242_);
    crate::leanh::lean_dec(v_i_3242_);
    v_stop_boxed_3246_ = crate::leanh::lean_unbox_usize(v_stop_3243_);
    crate::leanh::lean_dec(v_stop_3243_);
    v_res_3247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__2(v_as_3241_, v_i_boxed_3245_, v_stop_boxed_3246_, v_b_3244_);
    crate::leanh::lean_dec_ref(v_as_3241_);
    return v_res_3247_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__3(
    mut v_as_3248_: *mut crate::leanh::LeanObject,
    mut v_i_3249_: usize,
    mut v_stop_3250_: usize,
) -> u8 {
    let mut v___x_3251_: u8 = 0;
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_appearsInTypeProof_3253_: u8 = 0;
    let mut v___x_3254_: usize = 0;
    let mut v___x_3255_: usize = 0;
    let mut v___x_3257_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3251_ = lean_usize_dec_eq(v_i_3249_, v_stop_3250_);
                if v___x_3251_ == 0 {
                    v___x_3252_ = lean_array_uget_borrowed(v_as_3248_, v_i_3249_);
                    v_appearsInTypeProof_3253_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_3252_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    if v_appearsInTypeProof_3253_ == 0 {
                        v___x_3254_ = 1usize;
                        v___x_3255_ = lean_usize_add(v_i_3249_, v___x_3254_);
                        v_i_3249_ = v___x_3255_;
                        state = 0;
                        continue;
                    } else {
                        return v_appearsInTypeProof_3253_;
                    }
                } else {
                    v___x_3257_ = 0;
                    return v___x_3257_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__3___boxed(
    mut v_as_3258_: *mut crate::leanh::LeanObject,
    mut v_i_3259_: *mut crate::leanh::LeanObject,
    mut v_stop_3260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3261_: usize = 0;
    let mut v_stop_boxed_3262_: usize = 0;
    let mut v_res_3263_: u8 = 0;
    let mut v_r_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3261_ = crate::leanh::lean_unbox_usize(v_i_3259_);
    crate::leanh::lean_dec(v_i_3259_);
    v_stop_boxed_3262_ = crate::leanh::lean_unbox_usize(v_stop_3260_);
    crate::leanh::lean_dec(v_stop_3260_);
    v_res_3263_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__3(v_as_3258_, v_i_boxed_3261_, v_stop_boxed_3262_);
    crate::leanh::lean_dec_ref(v_as_3258_);
    v_r_3264_ = crate::leanh::lean_box((v_res_3263_) as usize);
    return v_r_3264_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__0(
    mut v_sz_3265_: usize,
    mut v_i_3266_: usize,
    mut v_bs_3267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3268_: u8 = 0;
    let mut v_v_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_x3f_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: usize = 0;
    let mut v___x_3277_: usize = 0;
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_appearsInTypeProof_3282_: u8 = 0;
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3288_: u8 = 0;
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3304_: u8 = 0;
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3268_ = lean_usize_dec_lt(v_i_3266_, v_sz_3265_);
                if v___x_3268_ == 0 {
                    return v_bs_3267_;
                } else {
                    v_v_3269_ = lean_array_uget(v_bs_3267_, v_i_3266_);
                    v_type_x3f_3270_ = crate::leanh::lean_ctor_get(v_v_3269_, 1);
                    crate::leanh::lean_inc(v_type_x3f_3270_);
                    v_idx_3271_ = crate::leanh::lean_ctor_get(v_v_3269_, 2);
                    v___x_3272_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3273_ = lean_array_uset(v_bs_3267_, v_i_3266_, v___x_3272_);
                    if crate::leanh::lean_obj_tag(v_type_x3f_3270_) == 1 {
                        v_val_3285_ = crate::leanh::lean_ctor_get(v_type_x3f_3270_, 0);
                        v_isSharedCheck_3304_ =
                            (!crate::leanh::lean_is_exclusive(v_type_x3f_3270_)) as u8;
                        if v_isSharedCheck_3304_ == 0 {
                            v___x_3287_ = v_type_x3f_3270_;
                            v_isShared_3288_ = v_isSharedCheck_3304_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_3285_);
                            crate::leanh::lean_dec(v_type_x3f_3270_);
                            v___x_3287_ = crate::leanh::lean_box(0);
                            v_isShared_3288_ = v_isSharedCheck_3304_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_type_x3f_3270_);
                        v___x_3305_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9_once), _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__9);
                        v___x_3306_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3307_ = lean_nat_add(v_idx_3271_, v___x_3306_);
                        v___x_3308_ = l_Nat_reprFast(v___x_3307_);
                        v___x_3309_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3309_, 0, v___x_3308_);
                        v___x_3310_ = l_Lean_MessageData_ofFormat(v___x_3309_);
                        v___x_3311_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3311_, 0, v___x_3305_);
                        crate::leanh::lean_ctor_set(v___x_3311_, 1, v___x_3310_);
                        v___y_3281_ = v___x_3311_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3276_ = 1usize;
                v___x_3277_ = lean_usize_add(v_i_3266_, v___x_3276_);
                v___x_3278_ = lean_array_uset(v_bs_x27_3273_, v_i_3266_, v___y_3275_);
                v_i_3266_ = v___x_3277_;
                v_bs_3267_ = v___x_3278_;
                state = 0;
                continue;
            }
            2 => {
                v_appearsInTypeProof_3282_ = crate::leanh::lean_ctor_get_uint8(
                    v_v_3269_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec(v_v_3269_);
                if v_appearsInTypeProof_3282_ == 0 {
                    v___y_3275_ = v___y_3281_;
                    state = 1;
                    continue;
                } else {
                    v___x_3283_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1_once), _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__1);
                    v_msg_3284_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_msg_3284_, 0, v___y_3281_);
                    crate::leanh::lean_ctor_set(v_msg_3284_, 1, v___x_3283_);
                    v___y_3275_ = v_msg_3284_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_3289_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3_once), _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__3);
                v___x_3290_ = l_Lean_MessageData_ofExpr(v_val_3285_);
                v___x_3291_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3291_, 0, v___x_3289_);
                crate::leanh::lean_ctor_set(v___x_3291_, 1, v___x_3290_);
                v___x_3292_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5_once), _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__5);
                v___x_3293_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3293_, 0, v___x_3291_);
                crate::leanh::lean_ctor_set(v___x_3293_, 1, v___x_3292_);
                v___x_3294_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3295_ = lean_nat_add(v_idx_3271_, v___x_3294_);
                v___x_3296_ = l_Nat_reprFast(v___x_3295_);
                if v_isShared_3288_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3287_, 3);
                    crate::leanh::lean_ctor_set(v___x_3287_, 0, v___x_3296_);
                    v___x_3298_ = v___x_3287_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3303_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3303_, 0, v___x_3296_);
                    v___x_3298_ = v_reuseFailAlloc_3303_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3299_ = l_Lean_MessageData_ofFormat(v___x_3298_);
                v___x_3300_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3300_, 0, v___x_3293_);
                crate::leanh::lean_ctor_set(v___x_3300_, 1, v___x_3299_);
                v___x_3301_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7_once), _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_instToMessageDataParameter___lam__0___closed__7);
                v___x_3302_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3302_, 0, v___x_3300_);
                crate::leanh::lean_ctor_set(v___x_3302_, 1, v___x_3301_);
                v___y_3281_ = v___x_3302_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__0___boxed(
    mut v_sz_3312_: *mut crate::leanh::LeanObject,
    mut v_i_3313_: *mut crate::leanh::LeanObject,
    mut v_bs_3314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3315_: usize = 0;
    let mut v_i_boxed_3316_: usize = 0;
    let mut v_res_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3315_ = crate::leanh::lean_unbox_usize(v_sz_3312_);
    crate::leanh::lean_dec(v_sz_3312_);
    v_i_boxed_3316_ = crate::leanh::lean_unbox_usize(v_i_3313_);
    crate::leanh::lean_dec(v_i_3313_);
    v_res_3317_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__0(v_sz_boxed_3315_, v_i_boxed_3316_, v_bs_3314_);
    return v_res_3317_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3319_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___closed__0;
    v___x_3320_ = l_Lean_stringToMessageData(v___x_3319_);
    return v___x_3320_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1(
    mut v_sz_3321_: usize,
    mut v_i_3322_: usize,
    mut v_bs_3323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3324_: u8 = 0;
    let mut v_v_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: usize = 0;
    let mut v___x_3331_: usize = 0;
    let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3324_ = lean_usize_dec_lt(v_i_3322_, v_sz_3321_);
                if v___x_3324_ == 0 {
                    return v_bs_3323_;
                } else {
                    v_v_3325_ = lean_array_uget(v_bs_3323_, v_i_3322_);
                    v___x_3326_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3327_ = lean_array_uset(v_bs_3323_, v_i_3322_, v___x_3326_);
                    v___x_3328_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___closed__1);
                    v___x_3329_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3329_, 0, v___x_3328_);
                    crate::leanh::lean_ctor_set(v___x_3329_, 1, v_v_3325_);
                    v___x_3330_ = 1usize;
                    v___x_3331_ = lean_usize_add(v_i_3322_, v___x_3330_);
                    v___x_3332_ = lean_array_uset(v_bs_x27_3327_, v_i_3322_, v___x_3329_);
                    v_i_3322_ = v___x_3331_;
                    v_bs_3323_ = v___x_3332_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1___boxed(
    mut v_sz_3334_: *mut crate::leanh::LeanObject,
    mut v_i_3335_: *mut crate::leanh::LeanObject,
    mut v_bs_3336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3337_: usize = 0;
    let mut v_i_boxed_3338_: usize = 0;
    let mut v_res_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3337_ = crate::leanh::lean_unbox_usize(v_sz_3334_);
    crate::leanh::lean_dec(v_sz_3334_);
    v_i_boxed_3338_ = crate::leanh::lean_unbox_usize(v_i_3335_);
    crate::leanh::lean_dec(v_i_3335_);
    v_res_3339_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1(v_sz_boxed_3337_, v_i_boxed_3338_, v_bs_3336_);
    return v_res_3339_;
}
pub unsafe fn _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3341_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__0;
    v___x_3342_ = l_Lean_stringToMessageData(v___x_3341_);
    return v___x_3342_;
}
pub unsafe fn _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3344_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__2;
    v___x_3345_ = l_Lean_stringToMessageData(v___x_3344_);
    return v___x_3345_;
}
pub unsafe fn _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3349_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__6;
    v___x_3350_ = l_Lean_stringToMessageData(v___x_3349_);
    return v___x_3350_;
}
pub unsafe fn _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3352_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__8;
    v___x_3353_ = l_Lean_stringToMessageData(v___x_3352_);
    return v___x_3353_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg(
    mut v_declName_3356_: *mut crate::leanh::LeanObject,
    mut v_unusedInstanceBinders_3357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3360_: usize = 0;
    let mut v___y_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3369_: usize = 0;
    let mut v___x_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: u8 = 0;
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: u8 = 0;
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: usize = 0;
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: usize = 0;
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3383_: usize = 0;
    let mut v___y_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3386_: u8 = 0;
    let mut v___y_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3395_: u8 = 0;
    let mut v_sz_3396_: usize = 0;
    let mut v___x_3397_: usize = 0;
    let mut v_unusedInstanceBinders_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: u8 = 0;
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: u8 = 0;
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: u8 = 0;
    let mut v___x_3412_: usize = 0;
    let mut v___x_3413_: usize = 0;
    let mut v___x_3414_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3358_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3410_ = lean_array_get_size(v_unusedInstanceBinders_3357_);
                v___x_3411_ = lean_nat_dec_lt(v___x_3358_, v___x_3410_);
                if v___x_3411_ == 0 {
                    v___y_3395_ = v___x_3411_;
                    state = 3;
                    continue;
                } else {
                    if v___x_3411_ == 0 {
                        v___y_3395_ = v___x_3411_;
                        state = 3;
                        continue;
                    } else {
                        v___x_3412_ = 0usize;
                        v___x_3413_ = lean_usize_of_nat(v___x_3410_);
                        v___x_3414_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__3(v_unusedInstanceBinders_3357_, v___x_3412_, v___x_3413_);
                        v___y_3395_ = v___x_3414_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_3363_);
                v___x_3364_ = l_Lean_stringToMessageData(v___y_3363_);
                v___x_3365_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3365_, 0, v___y_3362_);
                crate::leanh::lean_ctor_set(v___x_3365_, 1, v___x_3364_);
                v___x_3366_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__1_once), _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__1);
                v___x_3367_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3367_, 0, v___x_3365_);
                crate::leanh::lean_ctor_set(v___x_3367_, 1, v___x_3366_);
                v___x_3368_ = l_Lean_MessageData_nil;
                v_sz_3369_ = lean_array_size(v___y_3361_);
                v___x_3370_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__1(v_sz_3369_, v___y_3360_, v___y_3361_);
                v___x_3371_ = lean_array_get_size(v___x_3370_);
                v___x_3372_ = lean_nat_dec_lt(v___x_3358_, v___x_3371_);
                if v___x_3372_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3370_);
                    v___x_3373_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3373_, 0, v___x_3367_);
                    crate::leanh::lean_ctor_set(v___x_3373_, 1, v___x_3368_);
                    return v___x_3373_;
                } else {
                    v___x_3374_ = lean_nat_dec_le(v___x_3371_, v___x_3371_);
                    if v___x_3374_ == 0 {
                        if v___x_3372_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_3370_);
                            v___x_3375_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3375_, 0, v___x_3367_);
                            crate::leanh::lean_ctor_set(v___x_3375_, 1, v___x_3368_);
                            return v___x_3375_;
                        } else {
                            v___x_3376_ = lean_usize_of_nat(v___x_3371_);
                            v___x_3377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__2(v___x_3370_, v___y_3360_, v___x_3376_, v___x_3368_);
                            crate::leanh::lean_dec_ref(v___x_3370_);
                            v___x_3378_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3378_, 0, v___x_3367_);
                            crate::leanh::lean_ctor_set(v___x_3378_, 1, v___x_3377_);
                            return v___x_3378_;
                        }
                    } else {
                        v___x_3379_ = lean_usize_of_nat(v___x_3371_);
                        v___x_3380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__2(v___x_3370_, v___y_3360_, v___x_3379_, v___x_3368_);
                        crate::leanh::lean_dec_ref(v___x_3370_);
                        v___x_3381_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3381_, 0, v___x_3367_);
                        crate::leanh::lean_ctor_set(v___x_3381_, 1, v___x_3380_);
                        return v___x_3381_;
                    }
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v___y_3387_);
                v___x_3388_ = l_Lean_stringToMessageData(v___y_3387_);
                v___x_3389_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3389_, 0, v___y_3385_);
                crate::leanh::lean_ctor_set(v___x_3389_, 1, v___x_3388_);
                v___x_3390_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__3_once), _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__3);
                v___x_3391_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3391_, 0, v___x_3389_);
                crate::leanh::lean_ctor_set(v___x_3391_, 1, v___x_3390_);
                if v___y_3386_ == 0 {
                    v___x_3392_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__4;
                    v___y_3360_ = v___y_3383_;
                    v___y_3361_ = v___y_3384_;
                    v___y_3362_ = v___x_3391_;
                    v___y_3363_ = v___x_3392_;
                    state = 1;
                    continue;
                } else {
                    v___x_3393_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__5;
                    v___y_3360_ = v___y_3383_;
                    v___y_3361_ = v___y_3384_;
                    v___y_3362_ = v___x_3391_;
                    v___y_3363_ = v___x_3393_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_sz_3396_ = lean_array_size(v_unusedInstanceBinders_3357_);
                v___x_3397_ = 0usize;
                v_unusedInstanceBinders_3398_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg_spec__0(v_sz_3396_, v___x_3397_, v_unusedInstanceBinders_3357_);
                v___x_3399_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__7_once), _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__7);
                v___x_3400_ = 0;
                v___x_3401_ = l_Lean_MessageData_ofConstName(v_declName_3356_, v___x_3400_);
                v___x_3402_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3402_, 0, v___x_3399_);
                crate::leanh::lean_ctor_set(v___x_3402_, 1, v___x_3401_);
                v___x_3403_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__9_once), _init_l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__9);
                v___x_3404_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3404_, 0, v___x_3402_);
                crate::leanh::lean_ctor_set(v___x_3404_, 1, v___x_3403_);
                v___x_3405_ = lean_array_get_size(v_unusedInstanceBinders_3398_);
                v___x_3406_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3407_ = lean_nat_dec_eq(v___x_3405_, v___x_3406_);
                if v___x_3407_ == 0 {
                    v___x_3408_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__10;
                    v___y_3383_ = v___x_3397_;
                    v___y_3384_ = v_unusedInstanceBinders_3398_;
                    v___y_3385_ = v___x_3404_;
                    v___y_3386_ = v___y_3395_;
                    v___y_3387_ = v___x_3408_;
                    state = 2;
                    continue;
                } else {
                    v___x_3409_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__11;
                    v___y_3383_ = v___x_3397_;
                    v___y_3384_ = v_unusedInstanceBinders_3398_;
                    v___y_3385_ = v___x_3404_;
                    v___y_3386_ = v___y_3395_;
                    v___y_3387_ = v___x_3409_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___lam__0(
    mut v_subExpr_3415_: *mut crate::leanh::LeanObject,
    mut v___y_3416_: *mut crate::leanh::LeanObject,
    mut v___y_3417_: *mut crate::leanh::LeanObject,
    mut v___y_3418_: *mut crate::leanh::LeanObject,
    mut v___y_3419_: *mut crate::leanh::LeanObject,
    mut v___y_3420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: u8 = 0;
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3432_: u8 = 0;
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3439_: u8 = 0;
    let mut v___x_3440_: u8 = 0;
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: u8 = 0;
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3450_: u8 = 0;
    let mut v_a_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: u8 = 0;
    let mut v___x_3453_: u8 = 0;
    let mut v___x_3454_: u8 = 0;
    let mut v___x_3455_: u8 = 0;
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3453_ = l_Lean_Expr_hasFVar(v_subExpr_3415_);
                if v___x_3453_ == 0 {
                    v___y_3432_ = v___x_3453_;
                    state = 2;
                    continue;
                } else {
                    v___x_3454_ = l_Lean_Expr_isSorry(v_subExpr_3415_);
                    if v___x_3454_ == 0 {
                        v___y_3432_ = v___x_3453_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_subExpr_3415_);
                        v___x_3455_ = 0;
                        v___x_3456_ = crate::leanh::lean_box((v___x_3455_) as usize);
                        v___x_3457_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3457_, 0, v___x_3456_);
                        return v___x_3457_;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_subExpr_3415_) == 1 {
                    crate::leanh::lean_dec_ref(v___y_3423_);
                    v_fvarId_3424_ = crate::leanh::lean_ctor_get(v_subExpr_3415_, 0);
                    crate::leanh::lean_inc(v_fvarId_3424_);
                    crate::leanh::lean_dec_ref_known(v_subExpr_3415_, 1);
                    v___x_3425_ = lean_st_ref_take(v___y_3416_);
                    v___x_3426_ = l_Lean_FVarIdSet_insert(v___x_3425_, v_fvarId_3424_);
                    v___x_3427_ = lean_st_ref_set(v___y_3416_, v___x_3426_);
                    v___x_3428_ = 0;
                    v___x_3429_ = crate::leanh::lean_box((v___x_3428_) as usize);
                    v___x_3430_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3430_, 0, v___x_3429_);
                    return v___x_3430_;
                } else {
                    crate::leanh::lean_dec_ref(v_subExpr_3415_);
                    return v___y_3423_;
                }
            }
            2 => {
                if v___y_3432_ == 0 {
                    crate::leanh::lean_dec_ref(v_subExpr_3415_);
                    v___x_3433_ = crate::leanh::lean_box((v___y_3432_) as usize);
                    v___x_3434_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3434_, 0, v___x_3433_);
                    return v___x_3434_;
                } else {
                    crate::leanh::lean_inc_ref(v_subExpr_3415_);
                    v___x_3435_ = l_Lean_Meta_isProof(
                        v_subExpr_3415_,
                        v___y_3417_,
                        v___y_3418_,
                        v___y_3419_,
                        v___y_3420_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3435_) == 0 {
                        v_a_3436_ = crate::leanh::lean_ctor_get(v___x_3435_, 0);
                        v_isSharedCheck_3450_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3435_)) as u8;
                        if v_isSharedCheck_3450_ == 0 {
                            v___x_3438_ = v___x_3435_;
                            v_isShared_3439_ = v_isSharedCheck_3450_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3436_);
                            crate::leanh::lean_dec(v___x_3435_);
                            v___x_3438_ = crate::leanh::lean_box(0);
                            v_isShared_3439_ = v_isSharedCheck_3450_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_3435_) == 0 {
                            v_a_3451_ = crate::leanh::lean_ctor_get(v___x_3435_, 0);
                            crate::leanh::lean_inc(v_a_3451_);
                            v___x_3452_ = (crate::leanh::lean_unbox(v_a_3451_) as u8);
                            crate::leanh::lean_dec(v_a_3451_);
                            if v___x_3452_ == 0 {
                                crate::leanh::lean_dec_ref(v_subExpr_3415_);
                                return v___x_3435_;
                            } else {
                                v___y_3423_ = v___x_3435_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_subExpr_3415_);
                            return v___x_3435_;
                        }
                    }
                }
            }
            3 => {
                v___x_3440_ = (crate::leanh::lean_unbox(v_a_3436_) as u8);
                crate::leanh::lean_dec(v_a_3436_);
                if v___x_3440_ == 0 {
                    v___x_3441_ = crate::leanh::lean_box((v___y_3432_) as usize);
                    if v_isShared_3439_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3438_, 0, v___x_3441_);
                        v___x_3443_ = v___x_3438_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3444_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3441_);
                        v___x_3443_ = v_reuseFailAlloc_3444_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_subExpr_3415_);
                    v___x_3445_ = 0;
                    v___x_3446_ = crate::leanh::lean_box((v___x_3445_) as usize);
                    if v_isShared_3439_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3438_, 0, v___x_3446_);
                        v___x_3448_ = v___x_3438_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3449_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3446_);
                        v___x_3448_ = v_reuseFailAlloc_3449_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v___y_3423_ = v___x_3443_;
                state = 1;
                continue;
            }
            5 => {
                return v___x_3448_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___lam__0___boxed(
    mut v_subExpr_3458_: *mut crate::leanh::LeanObject,
    mut v___y_3459_: *mut crate::leanh::LeanObject,
    mut v___y_3460_: *mut crate::leanh::LeanObject,
    mut v___y_3461_: *mut crate::leanh::LeanObject,
    mut v___y_3462_: *mut crate::leanh::LeanObject,
    mut v___y_3463_: *mut crate::leanh::LeanObject,
    mut v___y_3464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3465_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___lam__0(v_subExpr_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
    crate::leanh::lean_dec(v___y_3463_);
    crate::leanh::lean_dec_ref(v___y_3462_);
    crate::leanh::lean_dec(v___y_3461_);
    crate::leanh::lean_dec_ref(v___y_3460_);
    crate::leanh::lean_dec(v___y_3459_);
    return v_res_3465_;
}
pub unsafe fn l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___lam__0(
    mut v_00_u03b1_3466_: *mut crate::leanh::LeanObject,
    mut v_x_3467_: *mut crate::leanh::LeanObject,
    mut v___y_3468_: *mut crate::leanh::LeanObject,
    mut v___y_3469_: *mut crate::leanh::LeanObject,
    mut v___y_3470_: *mut crate::leanh::LeanObject,
    mut v___y_3471_: *mut crate::leanh::LeanObject,
    mut v___y_3472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3474_ = crate::leanh::lean_apply_1(v_x_3467_, crate::leanh::lean_box(0));
    v___x_3475_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3475_, 0, v___x_3474_);
    return v___x_3475_;
}
pub unsafe fn l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___lam__0___boxed(
    mut v_00_u03b1_3476_: *mut crate::leanh::LeanObject,
    mut v_x_3477_: *mut crate::leanh::LeanObject,
    mut v___y_3478_: *mut crate::leanh::LeanObject,
    mut v___y_3479_: *mut crate::leanh::LeanObject,
    mut v___y_3480_: *mut crate::leanh::LeanObject,
    mut v___y_3481_: *mut crate::leanh::LeanObject,
    mut v___y_3482_: *mut crate::leanh::LeanObject,
    mut v___y_3483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3484_ = l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___lam__0(v_00_u03b1_3476_, v_x_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
    crate::leanh::lean_dec(v___y_3482_);
    crate::leanh::lean_dec_ref(v___y_3481_);
    crate::leanh::lean_dec(v___y_3480_);
    crate::leanh::lean_dec_ref(v___y_3479_);
    crate::leanh::lean_dec(v___y_3478_);
    return v_res_3484_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___lam__0(
    mut v_k_3485_: *mut crate::leanh::LeanObject,
    mut v___y_3486_: *mut crate::leanh::LeanObject,
    mut v___y_3487_: *mut crate::leanh::LeanObject,
    mut v_b_3488_: *mut crate::leanh::LeanObject,
    mut v___y_3489_: *mut crate::leanh::LeanObject,
    mut v___y_3490_: *mut crate::leanh::LeanObject,
    mut v___y_3491_: *mut crate::leanh::LeanObject,
    mut v___y_3492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_3492_);
    crate::leanh::lean_inc_ref(v___y_3491_);
    crate::leanh::lean_inc(v___y_3490_);
    crate::leanh::lean_inc_ref(v___y_3489_);
    crate::leanh::lean_inc(v___y_3487_);
    crate::leanh::lean_inc(v___y_3486_);
    v___x_3494_ = crate::leanh::lean_apply_8(
        v_k_3485_,
        v_b_3488_,
        v___y_3486_,
        v___y_3487_,
        v___y_3489_,
        v___y_3490_,
        v___y_3491_,
        v___y_3492_,
        crate::leanh::lean_box(0),
    );
    return v___x_3494_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___lam__0___boxed(
    mut v_k_3495_: *mut crate::leanh::LeanObject,
    mut v___y_3496_: *mut crate::leanh::LeanObject,
    mut v___y_3497_: *mut crate::leanh::LeanObject,
    mut v_b_3498_: *mut crate::leanh::LeanObject,
    mut v___y_3499_: *mut crate::leanh::LeanObject,
    mut v___y_3500_: *mut crate::leanh::LeanObject,
    mut v___y_3501_: *mut crate::leanh::LeanObject,
    mut v___y_3502_: *mut crate::leanh::LeanObject,
    mut v___y_3503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3504_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___lam__0(v_k_3495_, v___y_3496_, v___y_3497_, v_b_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
    crate::leanh::lean_dec(v___y_3502_);
    crate::leanh::lean_dec_ref(v___y_3501_);
    crate::leanh::lean_dec(v___y_3500_);
    crate::leanh::lean_dec_ref(v___y_3499_);
    crate::leanh::lean_dec(v___y_3497_);
    crate::leanh::lean_dec(v___y_3496_);
    return v_res_3504_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(
    mut v_name_3505_: *mut crate::leanh::LeanObject,
    mut v_bi_3506_: u8,
    mut v_type_3507_: *mut crate::leanh::LeanObject,
    mut v_k_3508_: *mut crate::leanh::LeanObject,
    mut v_kind_3509_: u8,
    mut v___y_3510_: *mut crate::leanh::LeanObject,
    mut v___y_3511_: *mut crate::leanh::LeanObject,
    mut v___y_3512_: *mut crate::leanh::LeanObject,
    mut v___y_3513_: *mut crate::leanh::LeanObject,
    mut v___y_3514_: *mut crate::leanh::LeanObject,
    mut v___y_3515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3522_: u8 = 0;
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3526_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_3511_);
                crate::leanh::lean_inc(v___y_3510_);
                v___f_3517_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 3);
                crate::leanh::lean_closure_set(v___f_3517_, 0, v_k_3508_);
                crate::leanh::lean_closure_set(v___f_3517_, 1, v___y_3510_);
                crate::leanh::lean_closure_set(v___f_3517_, 2, v___y_3511_);
                v___x_3518_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_3505_,
                    v_bi_3506_,
                    v_type_3507_,
                    v___f_3517_,
                    v_kind_3509_,
                    v___y_3512_,
                    v___y_3513_,
                    v___y_3514_,
                    v___y_3515_,
                );
                if crate::leanh::lean_obj_tag(v___x_3518_) == 0 {
                    return v___x_3518_;
                } else {
                    v_a_3519_ = crate::leanh::lean_ctor_get(v___x_3518_, 0);
                    v_isSharedCheck_3526_ = (!crate::leanh::lean_is_exclusive(v___x_3518_)) as u8;
                    if v_isSharedCheck_3526_ == 0 {
                        v___x_3521_ = v___x_3518_;
                        v_isShared_3522_ = v_isSharedCheck_3526_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3519_);
                        crate::leanh::lean_dec(v___x_3518_);
                        v___x_3521_ = crate::leanh::lean_box(0);
                        v_isShared_3522_ = v_isSharedCheck_3526_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3522_ == 0 {
                    v___x_3524_ = v___x_3521_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3525_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_a_3519_);
                    v___x_3524_ = v_reuseFailAlloc_3525_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3524_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___boxed(
    mut v_name_3527_: *mut crate::leanh::LeanObject,
    mut v_bi_3528_: *mut crate::leanh::LeanObject,
    mut v_type_3529_: *mut crate::leanh::LeanObject,
    mut v_k_3530_: *mut crate::leanh::LeanObject,
    mut v_kind_3531_: *mut crate::leanh::LeanObject,
    mut v___y_3532_: *mut crate::leanh::LeanObject,
    mut v___y_3533_: *mut crate::leanh::LeanObject,
    mut v___y_3534_: *mut crate::leanh::LeanObject,
    mut v___y_3535_: *mut crate::leanh::LeanObject,
    mut v___y_3536_: *mut crate::leanh::LeanObject,
    mut v___y_3537_: *mut crate::leanh::LeanObject,
    mut v___y_3538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_3539_: u8 = 0;
    let mut v_kind_boxed_3540_: u8 = 0;
    let mut v_res_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_3539_ = (crate::leanh::lean_unbox(v_bi_3528_) as u8);
    v_kind_boxed_3540_ = (crate::leanh::lean_unbox(v_kind_3531_) as u8);
    v_res_3541_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_name_3527_, v_bi_boxed_3539_, v_type_3529_, v_k_3530_, v_kind_boxed_3540_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_);
    crate::leanh::lean_dec(v___y_3537_);
    crate::leanh::lean_dec_ref(v___y_3536_);
    crate::leanh::lean_dec(v___y_3535_);
    crate::leanh::lean_dec_ref(v___y_3534_);
    crate::leanh::lean_dec(v___y_3533_);
    crate::leanh::lean_dec(v___y_3532_);
    return v_res_3541_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8___lam__0___boxed(
    mut v_fvars_3542_: *mut crate::leanh::LeanObject,
    mut v_f_3543_: *mut crate::leanh::LeanObject,
    mut v_body_3544_: *mut crate::leanh::LeanObject,
    mut v_x_3545_: *mut crate::leanh::LeanObject,
    mut v___y_3546_: *mut crate::leanh::LeanObject,
    mut v___y_3547_: *mut crate::leanh::LeanObject,
    mut v___y_3548_: *mut crate::leanh::LeanObject,
    mut v___y_3549_: *mut crate::leanh::LeanObject,
    mut v___y_3550_: *mut crate::leanh::LeanObject,
    mut v___y_3551_: *mut crate::leanh::LeanObject,
    mut v___y_3552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3553_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8___lam__0(v_fvars_3542_, v_f_3543_, v_body_3544_, v_x_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_);
    crate::leanh::lean_dec(v___y_3551_);
    crate::leanh::lean_dec_ref(v___y_3550_);
    crate::leanh::lean_dec(v___y_3549_);
    crate::leanh::lean_dec_ref(v___y_3548_);
    crate::leanh::lean_dec(v___y_3547_);
    crate::leanh::lean_dec(v___y_3546_);
    return v_res_3553_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8(
    mut v_f_3554_: *mut crate::leanh::LeanObject,
    mut v_fvars_3555_: *mut crate::leanh::LeanObject,
    mut v_a_3556_: *mut crate::leanh::LeanObject,
    mut v___y_3557_: *mut crate::leanh::LeanObject,
    mut v___y_3558_: *mut crate::leanh::LeanObject,
    mut v___y_3559_: *mut crate::leanh::LeanObject,
    mut v___y_3560_: *mut crate::leanh::LeanObject,
    mut v___y_3561_: *mut crate::leanh::LeanObject,
    mut v___y_3562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_a_3556_) == 7 {
        let mut v_binderName_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderType_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_3567_: u8 = 0;
        let mut v_d_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_binderName_3564_ = crate::leanh::lean_ctor_get(v_a_3556_, 0);
        crate::leanh::lean_inc(v_binderName_3564_);
        v_binderType_3565_ = crate::leanh::lean_ctor_get(v_a_3556_, 1);
        crate::leanh::lean_inc_ref(v_binderType_3565_);
        v_body_3566_ = crate::leanh::lean_ctor_get(v_a_3556_, 2);
        crate::leanh::lean_inc_ref(v_body_3566_);
        v_binderInfo_3567_ = crate::leanh::lean_ctor_get_uint8(
            v_a_3556_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        );
        crate::leanh::lean_dec_ref_known(v_a_3556_, 3);
        v_d_3568_ = lean_expr_instantiate_rev(v_binderType_3565_, v_fvars_3555_);
        crate::leanh::lean_dec_ref(v_binderType_3565_);
        crate::leanh::lean_inc_ref(v_f_3554_);
        crate::leanh::lean_inc(v___y_3562_);
        crate::leanh::lean_inc_ref(v___y_3561_);
        crate::leanh::lean_inc(v___y_3560_);
        crate::leanh::lean_inc_ref(v___y_3559_);
        crate::leanh::lean_inc(v___y_3558_);
        crate::leanh::lean_inc(v___y_3557_);
        crate::leanh::lean_inc_ref(v_d_3568_);
        v___x_3569_ = crate::leanh::lean_apply_8(
            v_f_3554_,
            v_d_3568_,
            v___y_3557_,
            v___y_3558_,
            v___y_3559_,
            v___y_3560_,
            v___y_3561_,
            v___y_3562_,
            crate::leanh::lean_box(0),
        );
        if crate::leanh::lean_obj_tag(v___x_3569_) == 0 {
            let mut v___f_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3571_: u8 = 0;
            let mut v___x_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_3569_, 1);
            v___f_3570_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8___lam__0___boxed as *mut core::ffi::c_void, 11, 3);
            crate::leanh::lean_closure_set(v___f_3570_, 0, v_fvars_3555_);
            crate::leanh::lean_closure_set(v___f_3570_, 1, v_f_3554_);
            crate::leanh::lean_closure_set(v___f_3570_, 2, v_body_3566_);
            v___x_3571_ = 0;
            v___x_3572_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_binderName_3564_, v_binderInfo_3567_, v_d_3568_, v___f_3570_, v___x_3571_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
            return v___x_3572_;
        } else {
            crate::leanh::lean_dec_ref(v_d_3568_);
            crate::leanh::lean_dec_ref(v_body_3566_);
            crate::leanh::lean_dec(v_binderName_3564_);
            crate::leanh::lean_dec_ref(v_fvars_3555_);
            crate::leanh::lean_dec_ref(v_f_3554_);
            return v___x_3569_;
        }
    } else {
        let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3573_ = lean_expr_instantiate_rev(v_a_3556_, v_fvars_3555_);
        crate::leanh::lean_dec_ref(v_fvars_3555_);
        crate::leanh::lean_dec_ref(v_a_3556_);
        crate::leanh::lean_inc(v___y_3562_);
        crate::leanh::lean_inc_ref(v___y_3561_);
        crate::leanh::lean_inc(v___y_3560_);
        crate::leanh::lean_inc_ref(v___y_3559_);
        crate::leanh::lean_inc(v___y_3558_);
        crate::leanh::lean_inc(v___y_3557_);
        v___x_3574_ = crate::leanh::lean_apply_8(
            v_f_3554_,
            v___x_3573_,
            v___y_3557_,
            v___y_3558_,
            v___y_3559_,
            v___y_3560_,
            v___y_3561_,
            v___y_3562_,
            crate::leanh::lean_box(0),
        );
        return v___x_3574_;
    }
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8___lam__0(
    mut v_fvars_3575_: *mut crate::leanh::LeanObject,
    mut v_f_3576_: *mut crate::leanh::LeanObject,
    mut v_body_3577_: *mut crate::leanh::LeanObject,
    mut v_x_3578_: *mut crate::leanh::LeanObject,
    mut v___y_3579_: *mut crate::leanh::LeanObject,
    mut v___y_3580_: *mut crate::leanh::LeanObject,
    mut v___y_3581_: *mut crate::leanh::LeanObject,
    mut v___y_3582_: *mut crate::leanh::LeanObject,
    mut v___y_3583_: *mut crate::leanh::LeanObject,
    mut v___y_3584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3586_ = lean_array_push(v_fvars_3575_, v_x_3578_);
    v___x_3587_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8(v_f_3576_, v___x_3586_, v_body_3577_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_);
    return v___x_3587_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8___boxed(
    mut v_f_3588_: *mut crate::leanh::LeanObject,
    mut v_fvars_3589_: *mut crate::leanh::LeanObject,
    mut v_a_3590_: *mut crate::leanh::LeanObject,
    mut v___y_3591_: *mut crate::leanh::LeanObject,
    mut v___y_3592_: *mut crate::leanh::LeanObject,
    mut v___y_3593_: *mut crate::leanh::LeanObject,
    mut v___y_3594_: *mut crate::leanh::LeanObject,
    mut v___y_3595_: *mut crate::leanh::LeanObject,
    mut v___y_3596_: *mut crate::leanh::LeanObject,
    mut v___y_3597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3598_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8(v_f_3588_, v_fvars_3589_, v_a_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
    crate::leanh::lean_dec(v___y_3596_);
    crate::leanh::lean_dec_ref(v___y_3595_);
    crate::leanh::lean_dec(v___y_3594_);
    crate::leanh::lean_dec_ref(v___y_3593_);
    crate::leanh::lean_dec(v___y_3592_);
    crate::leanh::lean_dec(v___y_3591_);
    return v_res_3598_;
}
pub unsafe fn l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3(
    mut v_f_3601_: *mut crate::leanh::LeanObject,
    mut v_e_3602_: *mut crate::leanh::LeanObject,
    mut v___y_3603_: *mut crate::leanh::LeanObject,
    mut v___y_3604_: *mut crate::leanh::LeanObject,
    mut v___y_3605_: *mut crate::leanh::LeanObject,
    mut v___y_3606_: *mut crate::leanh::LeanObject,
    mut v___y_3607_: *mut crate::leanh::LeanObject,
    mut v___y_3608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3610_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3___closed__0;
    v___x_3611_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8(v_f_3601_, v___x_3610_, v_e_3602_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_);
    return v___x_3611_;
}
pub unsafe fn l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3___boxed(
    mut v_f_3612_: *mut crate::leanh::LeanObject,
    mut v_e_3613_: *mut crate::leanh::LeanObject,
    mut v___y_3614_: *mut crate::leanh::LeanObject,
    mut v___y_3615_: *mut crate::leanh::LeanObject,
    mut v___y_3616_: *mut crate::leanh::LeanObject,
    mut v___y_3617_: *mut crate::leanh::LeanObject,
    mut v___y_3618_: *mut crate::leanh::LeanObject,
    mut v___y_3619_: *mut crate::leanh::LeanObject,
    mut v___y_3620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3621_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3(v_f_3612_, v_e_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_);
    crate::leanh::lean_dec(v___y_3619_);
    crate::leanh::lean_dec_ref(v___y_3618_);
    crate::leanh::lean_dec(v___y_3617_);
    crate::leanh::lean_dec_ref(v___y_3616_);
    crate::leanh::lean_dec(v___y_3615_);
    crate::leanh::lean_dec(v___y_3614_);
    return v_res_3621_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6_spec__10___redArg(
    mut v_x_3622_: *mut crate::leanh::LeanObject,
    mut v_x_3623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3629_: u8 = 0;
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: u64 = 0;
    let mut v___x_3632_: u64 = 0;
    let mut v___x_3633_: u64 = 0;
    let mut v_fold_3634_: u64 = 0;
    let mut v___x_3635_: u64 = 0;
    let mut v___x_3636_: u64 = 0;
    let mut v___x_3637_: u64 = 0;
    let mut v___x_3638_: usize = 0;
    let mut v___x_3639_: usize = 0;
    let mut v___x_3640_: usize = 0;
    let mut v___x_3641_: usize = 0;
    let mut v___x_3642_: usize = 0;
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3649_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3623_) == 0 {
                    return v_x_3622_;
                } else {
                    v_key_3624_ = crate::leanh::lean_ctor_get(v_x_3623_, 0);
                    v_value_3625_ = crate::leanh::lean_ctor_get(v_x_3623_, 1);
                    v_tail_3626_ = crate::leanh::lean_ctor_get(v_x_3623_, 2);
                    v_isSharedCheck_3649_ = (!crate::leanh::lean_is_exclusive(v_x_3623_)) as u8;
                    if v_isSharedCheck_3649_ == 0 {
                        v___x_3628_ = v_x_3623_;
                        v_isShared_3629_ = v_isSharedCheck_3649_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3626_);
                        crate::leanh::lean_inc(v_value_3625_);
                        crate::leanh::lean_inc(v_key_3624_);
                        crate::leanh::lean_dec(v_x_3623_);
                        v___x_3628_ = crate::leanh::lean_box(0);
                        v_isShared_3629_ = v_isSharedCheck_3649_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3630_ = lean_array_get_size(v_x_3622_);
                v___x_3631_ = l_Lean_Expr_hash(v_key_3624_);
                v___x_3632_ = 32u64;
                v___x_3633_ = lean_uint64_shift_right(v___x_3631_, v___x_3632_);
                v_fold_3634_ = lean_uint64_xor(v___x_3631_, v___x_3633_);
                v___x_3635_ = 16u64;
                v___x_3636_ = lean_uint64_shift_right(v_fold_3634_, v___x_3635_);
                v___x_3637_ = lean_uint64_xor(v_fold_3634_, v___x_3636_);
                v___x_3638_ = lean_uint64_to_usize(v___x_3637_);
                v___x_3639_ = lean_usize_of_nat(v___x_3630_);
                v___x_3640_ = 1usize;
                v___x_3641_ = lean_usize_sub(v___x_3639_, v___x_3640_);
                v___x_3642_ = lean_usize_land(v___x_3638_, v___x_3641_);
                v___x_3643_ = lean_array_uget_borrowed(v_x_3622_, v___x_3642_);
                crate::leanh::lean_inc(v___x_3643_);
                if v_isShared_3629_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3628_, 2, v___x_3643_);
                    v___x_3645_ = v___x_3628_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3648_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_key_3624_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3648_, 1, v_value_3625_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3648_, 2, v___x_3643_);
                    v___x_3645_ = v_reuseFailAlloc_3648_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3646_ = lean_array_uset(v_x_3622_, v___x_3642_, v___x_3645_);
                v_x_3622_ = v___x_3646_;
                v_x_3623_ = v_tail_3626_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(
    mut v_i_3650_: *mut crate::leanh::LeanObject,
    mut v_source_3651_: *mut crate::leanh::LeanObject,
    mut v_target_3652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: u8 = 0;
    let mut v_es_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3653_ = lean_array_get_size(v_source_3651_);
                v___x_3654_ = lean_nat_dec_lt(v_i_3650_, v___x_3653_);
                if v___x_3654_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_3651_);
                    crate::leanh::lean_dec(v_i_3650_);
                    return v_target_3652_;
                } else {
                    v_es_3655_ = lean_array_fget(v_source_3651_, v_i_3650_);
                    v___x_3656_ = crate::leanh::lean_box(0);
                    v_source_3657_ = lean_array_fset(v_source_3651_, v_i_3650_, v___x_3656_);
                    v_target_3658_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6_spec__10___redArg(v_target_3652_, v_es_3655_);
                    v___x_3659_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3660_ = lean_nat_add(v_i_3650_, v___x_3659_);
                    crate::leanh::lean_dec(v_i_3650_);
                    v_i_3650_ = v___x_3660_;
                    v_source_3651_ = v_source_3657_;
                    v_target_3652_ = v_target_3658_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5___redArg(
    mut v_data_3662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3663_ = lean_array_get_size(v_data_3662_);
    v___x_3664_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3665_ = lean_nat_mul(v___x_3663_, v___x_3664_);
    v___x_3666_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3667_ = crate::leanh::lean_box(0);
    v___x_3668_ = lean_mk_array(v_nbuckets_3665_, v___x_3667_);
    v___x_3669_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v___x_3666_, v_data_3662_, v___x_3668_);
    return v___x_3669_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__6___redArg(
    mut v_a_3670_: *mut crate::leanh::LeanObject,
    mut v_b_3671_: *mut crate::leanh::LeanObject,
    mut v_x_3672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3678_: u8 = 0;
    let mut v___x_3679_: u8 = 0;
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3687_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3672_) == 0 {
                    crate::leanh::lean_dec(v_b_3671_);
                    crate::leanh::lean_dec_ref(v_a_3670_);
                    return v_x_3672_;
                } else {
                    v_key_3673_ = crate::leanh::lean_ctor_get(v_x_3672_, 0);
                    v_value_3674_ = crate::leanh::lean_ctor_get(v_x_3672_, 1);
                    v_tail_3675_ = crate::leanh::lean_ctor_get(v_x_3672_, 2);
                    v_isSharedCheck_3687_ = (!crate::leanh::lean_is_exclusive(v_x_3672_)) as u8;
                    if v_isSharedCheck_3687_ == 0 {
                        v___x_3677_ = v_x_3672_;
                        v_isShared_3678_ = v_isSharedCheck_3687_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3675_);
                        crate::leanh::lean_inc(v_value_3674_);
                        crate::leanh::lean_inc(v_key_3673_);
                        crate::leanh::lean_dec(v_x_3672_);
                        v___x_3677_ = crate::leanh::lean_box(0);
                        v_isShared_3678_ = v_isSharedCheck_3687_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3679_ = lean_expr_eqv(v_key_3673_, v_a_3670_);
                if v___x_3679_ == 0 {
                    v___x_3680_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__6___redArg(v_a_3670_, v_b_3671_, v_tail_3675_);
                    if v_isShared_3678_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3677_, 2, v___x_3680_);
                        v___x_3682_ = v___x_3677_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3683_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_key_3673_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3683_, 1, v_value_3674_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3683_, 2, v___x_3680_);
                        v___x_3682_ = v_reuseFailAlloc_3683_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_3674_);
                    crate::leanh::lean_dec(v_key_3673_);
                    if v_isShared_3678_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3677_, 1, v_b_3671_);
                        crate::leanh::lean_ctor_set(v___x_3677_, 0, v_a_3670_);
                        v___x_3685_ = v___x_3677_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3686_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_a_3670_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3686_, 1, v_b_3671_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3686_, 2, v_tail_3675_);
                        v___x_3685_ = v_reuseFailAlloc_3686_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3682_;
            }
            3 => {
                return v___x_3685_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4___redArg(
    mut v_a_3688_: *mut crate::leanh::LeanObject,
    mut v_x_3689_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3690_: u8 = 0;
    let mut v_key_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3689_) == 0 {
                    v___x_3690_ = 0;
                    return v___x_3690_;
                } else {
                    v_key_3691_ = crate::leanh::lean_ctor_get(v_x_3689_, 0);
                    v_tail_3692_ = crate::leanh::lean_ctor_get(v_x_3689_, 2);
                    v___x_3693_ = lean_expr_eqv(v_key_3691_, v_a_3688_);
                    if v___x_3693_ == 0 {
                        v_x_3689_ = v_tail_3692_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3693_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4___redArg___boxed(
    mut v_a_3695_: *mut crate::leanh::LeanObject,
    mut v_x_3696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3697_: u8 = 0;
    let mut v_r_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3697_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4___redArg(v_a_3695_, v_x_3696_);
    crate::leanh::lean_dec(v_x_3696_);
    crate::leanh::lean_dec_ref(v_a_3695_);
    v_r_3698_ = crate::leanh::lean_box((v_res_3697_) as usize);
    return v_r_3698_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2___redArg(
    mut v_m_3699_: *mut crate::leanh::LeanObject,
    mut v_a_3700_: *mut crate::leanh::LeanObject,
    mut v_b_3701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3706_: u8 = 0;
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: u64 = 0;
    let mut v___x_3709_: u64 = 0;
    let mut v___x_3710_: u64 = 0;
    let mut v_fold_3711_: u64 = 0;
    let mut v___x_3712_: u64 = 0;
    let mut v___x_3713_: u64 = 0;
    let mut v___x_3714_: u64 = 0;
    let mut v___x_3715_: usize = 0;
    let mut v___x_3716_: usize = 0;
    let mut v___x_3717_: usize = 0;
    let mut v___x_3718_: usize = 0;
    let mut v___x_3719_: usize = 0;
    let mut v_bkt_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: u8 = 0;
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: u8 = 0;
    let mut v_val_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3746_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3702_ = crate::leanh::lean_ctor_get(v_m_3699_, 0);
                v_buckets_3703_ = crate::leanh::lean_ctor_get(v_m_3699_, 1);
                v_isSharedCheck_3746_ = (!crate::leanh::lean_is_exclusive(v_m_3699_)) as u8;
                if v_isSharedCheck_3746_ == 0 {
                    v___x_3705_ = v_m_3699_;
                    v_isShared_3706_ = v_isSharedCheck_3746_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_3703_);
                    crate::leanh::lean_inc(v_size_3702_);
                    crate::leanh::lean_dec(v_m_3699_);
                    v___x_3705_ = crate::leanh::lean_box(0);
                    v_isShared_3706_ = v_isSharedCheck_3746_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3707_ = lean_array_get_size(v_buckets_3703_);
                v___x_3708_ = l_Lean_Expr_hash(v_a_3700_);
                v___x_3709_ = 32u64;
                v___x_3710_ = lean_uint64_shift_right(v___x_3708_, v___x_3709_);
                v_fold_3711_ = lean_uint64_xor(v___x_3708_, v___x_3710_);
                v___x_3712_ = 16u64;
                v___x_3713_ = lean_uint64_shift_right(v_fold_3711_, v___x_3712_);
                v___x_3714_ = lean_uint64_xor(v_fold_3711_, v___x_3713_);
                v___x_3715_ = lean_uint64_to_usize(v___x_3714_);
                v___x_3716_ = lean_usize_of_nat(v___x_3707_);
                v___x_3717_ = 1usize;
                v___x_3718_ = lean_usize_sub(v___x_3716_, v___x_3717_);
                v___x_3719_ = lean_usize_land(v___x_3715_, v___x_3718_);
                v_bkt_3720_ = lean_array_uget_borrowed(v_buckets_3703_, v___x_3719_);
                v___x_3721_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4___redArg(v_a_3700_, v_bkt_3720_);
                if v___x_3721_ == 0 {
                    v___x_3722_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_3723_ = lean_nat_add(v_size_3702_, v___x_3722_);
                    crate::leanh::lean_dec(v_size_3702_);
                    crate::leanh::lean_inc(v_bkt_3720_);
                    v___x_3724_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3724_, 0, v_a_3700_);
                    crate::leanh::lean_ctor_set(v___x_3724_, 1, v_b_3701_);
                    crate::leanh::lean_ctor_set(v___x_3724_, 2, v_bkt_3720_);
                    v_buckets_x27_3725_ =
                        lean_array_uset(v_buckets_3703_, v___x_3719_, v___x_3724_);
                    v___x_3726_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_3727_ = lean_nat_mul(v_size_x27_3723_, v___x_3726_);
                    v___x_3728_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_3729_ = lean_nat_div(v___x_3727_, v___x_3728_);
                    crate::leanh::lean_dec(v___x_3727_);
                    v___x_3730_ = lean_array_get_size(v_buckets_x27_3725_);
                    v___x_3731_ = lean_nat_dec_le(v___x_3729_, v___x_3730_);
                    crate::leanh::lean_dec(v___x_3729_);
                    if v___x_3731_ == 0 {
                        v_val_3732_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5___redArg(v_buckets_x27_3725_);
                        if v_isShared_3706_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3705_, 1, v_val_3732_);
                            crate::leanh::lean_ctor_set(v___x_3705_, 0, v_size_x27_3723_);
                            v___x_3734_ = v___x_3705_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3735_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3735_,
                                0,
                                v_size_x27_3723_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3735_, 1, v_val_3732_);
                            v___x_3734_ = v_reuseFailAlloc_3735_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3706_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3705_, 1, v_buckets_x27_3725_);
                            crate::leanh::lean_ctor_set(v___x_3705_, 0, v_size_x27_3723_);
                            v___x_3737_ = v___x_3705_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3738_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3738_,
                                0,
                                v_size_x27_3723_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3738_,
                                1,
                                v_buckets_x27_3725_,
                            );
                            v___x_3737_ = v_reuseFailAlloc_3738_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_3720_);
                    v___x_3739_ = crate::leanh::lean_box(0);
                    v_buckets_x27_3740_ =
                        lean_array_uset(v_buckets_3703_, v___x_3719_, v___x_3739_);
                    v___x_3741_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__6___redArg(v_a_3700_, v_b_3701_, v_bkt_3720_);
                    v___x_3742_ = lean_array_uset(v_buckets_x27_3740_, v___x_3719_, v___x_3741_);
                    if v_isShared_3706_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3705_, 1, v___x_3742_);
                        v___x_3744_ = v___x_3705_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3745_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_size_3702_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3745_, 1, v___x_3742_);
                        v___x_3744_ = v_reuseFailAlloc_3745_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3734_;
            }
            3 => {
                return v___x_3737_;
            }
            4 => {
                return v___x_3744_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__1(
    mut v_a_3747_: *mut crate::leanh::LeanObject,
    mut v_e_3748_: *mut crate::leanh::LeanObject,
    mut v_a_3749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3751_ = lean_st_ref_take(v_a_3747_);
    v___x_3752_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2___redArg(v___x_3751_, v_e_3748_, v_a_3749_);
    v___x_3753_ = lean_st_ref_set(v_a_3747_, v___x_3752_);
    v___x_3754_ = crate::leanh::lean_box(0);
    return v___x_3754_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__1___boxed(
    mut v_a_3755_: *mut crate::leanh::LeanObject,
    mut v_e_3756_: *mut crate::leanh::LeanObject,
    mut v_a_3757_: *mut crate::leanh::LeanObject,
    mut v___y_3758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3759_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__1(v_a_3755_, v_e_3756_, v_a_3757_);
    crate::leanh::lean_dec(v_a_3755_);
    return v_res_3759_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15___redArg(
    mut v_name_3760_: *mut crate::leanh::LeanObject,
    mut v_type_3761_: *mut crate::leanh::LeanObject,
    mut v_val_3762_: *mut crate::leanh::LeanObject,
    mut v_k_3763_: *mut crate::leanh::LeanObject,
    mut v_nondep_3764_: u8,
    mut v_kind_3765_: u8,
    mut v___y_3766_: *mut crate::leanh::LeanObject,
    mut v___y_3767_: *mut crate::leanh::LeanObject,
    mut v___y_3768_: *mut crate::leanh::LeanObject,
    mut v___y_3769_: *mut crate::leanh::LeanObject,
    mut v___y_3770_: *mut crate::leanh::LeanObject,
    mut v___y_3771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3778_: u8 = 0;
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3782_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_3767_);
                crate::leanh::lean_inc(v___y_3766_);
                v___f_3773_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 3);
                crate::leanh::lean_closure_set(v___f_3773_, 0, v_k_3763_);
                crate::leanh::lean_closure_set(v___f_3773_, 1, v___y_3766_);
                crate::leanh::lean_closure_set(v___f_3773_, 2, v___y_3767_);
                v___x_3774_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_3760_,
                    v_type_3761_,
                    v_val_3762_,
                    v___f_3773_,
                    v_nondep_3764_,
                    v_kind_3765_,
                    v___y_3768_,
                    v___y_3769_,
                    v___y_3770_,
                    v___y_3771_,
                );
                if crate::leanh::lean_obj_tag(v___x_3774_) == 0 {
                    return v___x_3774_;
                } else {
                    v_a_3775_ = crate::leanh::lean_ctor_get(v___x_3774_, 0);
                    v_isSharedCheck_3782_ = (!crate::leanh::lean_is_exclusive(v___x_3774_)) as u8;
                    if v_isSharedCheck_3782_ == 0 {
                        v___x_3777_ = v___x_3774_;
                        v_isShared_3778_ = v_isSharedCheck_3782_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3775_);
                        crate::leanh::lean_dec(v___x_3774_);
                        v___x_3777_ = crate::leanh::lean_box(0);
                        v_isShared_3778_ = v_isSharedCheck_3782_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3778_ == 0 {
                    v___x_3780_ = v___x_3777_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3781_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_a_3775_);
                    v___x_3780_ = v_reuseFailAlloc_3781_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3780_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15___redArg___boxed(
    mut v_name_3783_: *mut crate::leanh::LeanObject,
    mut v_type_3784_: *mut crate::leanh::LeanObject,
    mut v_val_3785_: *mut crate::leanh::LeanObject,
    mut v_k_3786_: *mut crate::leanh::LeanObject,
    mut v_nondep_3787_: *mut crate::leanh::LeanObject,
    mut v_kind_3788_: *mut crate::leanh::LeanObject,
    mut v___y_3789_: *mut crate::leanh::LeanObject,
    mut v___y_3790_: *mut crate::leanh::LeanObject,
    mut v___y_3791_: *mut crate::leanh::LeanObject,
    mut v___y_3792_: *mut crate::leanh::LeanObject,
    mut v___y_3793_: *mut crate::leanh::LeanObject,
    mut v___y_3794_: *mut crate::leanh::LeanObject,
    mut v___y_3795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nondep_boxed_3796_: u8 = 0;
    let mut v_kind_boxed_3797_: u8 = 0;
    let mut v_res_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_3796_ = (crate::leanh::lean_unbox(v_nondep_3787_) as u8);
    v_kind_boxed_3797_ = (crate::leanh::lean_unbox(v_kind_3788_) as u8);
    v_res_3798_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15___redArg(v_name_3783_, v_type_3784_, v_val_3785_, v_k_3786_, v_nondep_boxed_3796_, v_kind_boxed_3797_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
    crate::leanh::lean_dec(v___y_3794_);
    crate::leanh::lean_dec_ref(v___y_3793_);
    crate::leanh::lean_dec(v___y_3792_);
    crate::leanh::lean_dec_ref(v___y_3791_);
    crate::leanh::lean_dec(v___y_3790_);
    crate::leanh::lean_dec(v___y_3789_);
    return v_res_3798_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12___lam__0___boxed(
    mut v_fvars_3799_: *mut crate::leanh::LeanObject,
    mut v_f_3800_: *mut crate::leanh::LeanObject,
    mut v_body_3801_: *mut crate::leanh::LeanObject,
    mut v_x_3802_: *mut crate::leanh::LeanObject,
    mut v___y_3803_: *mut crate::leanh::LeanObject,
    mut v___y_3804_: *mut crate::leanh::LeanObject,
    mut v___y_3805_: *mut crate::leanh::LeanObject,
    mut v___y_3806_: *mut crate::leanh::LeanObject,
    mut v___y_3807_: *mut crate::leanh::LeanObject,
    mut v___y_3808_: *mut crate::leanh::LeanObject,
    mut v___y_3809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3810_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12___lam__0(v_fvars_3799_, v_f_3800_, v_body_3801_, v_x_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
    crate::leanh::lean_dec(v___y_3808_);
    crate::leanh::lean_dec_ref(v___y_3807_);
    crate::leanh::lean_dec(v___y_3806_);
    crate::leanh::lean_dec_ref(v___y_3805_);
    crate::leanh::lean_dec(v___y_3804_);
    crate::leanh::lean_dec(v___y_3803_);
    return v_res_3810_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12(
    mut v_f_3811_: *mut crate::leanh::LeanObject,
    mut v_fvars_3812_: *mut crate::leanh::LeanObject,
    mut v_a_3813_: *mut crate::leanh::LeanObject,
    mut v___y_3814_: *mut crate::leanh::LeanObject,
    mut v___y_3815_: *mut crate::leanh::LeanObject,
    mut v___y_3816_: *mut crate::leanh::LeanObject,
    mut v___y_3817_: *mut crate::leanh::LeanObject,
    mut v___y_3818_: *mut crate::leanh::LeanObject,
    mut v___y_3819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_a_3813_) == 8 {
        let mut v_declName_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_type_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_d_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_declName_3821_ = crate::leanh::lean_ctor_get(v_a_3813_, 0);
        crate::leanh::lean_inc(v_declName_3821_);
        v_type_3822_ = crate::leanh::lean_ctor_get(v_a_3813_, 1);
        crate::leanh::lean_inc_ref(v_type_3822_);
        v_value_3823_ = crate::leanh::lean_ctor_get(v_a_3813_, 2);
        crate::leanh::lean_inc_ref(v_value_3823_);
        v_body_3824_ = crate::leanh::lean_ctor_get(v_a_3813_, 3);
        crate::leanh::lean_inc_ref(v_body_3824_);
        crate::leanh::lean_dec_ref_known(v_a_3813_, 4);
        v_d_3825_ = lean_expr_instantiate_rev(v_type_3822_, v_fvars_3812_);
        crate::leanh::lean_dec_ref(v_type_3822_);
        crate::leanh::lean_inc_ref(v_f_3811_);
        crate::leanh::lean_inc(v___y_3819_);
        crate::leanh::lean_inc_ref(v___y_3818_);
        crate::leanh::lean_inc(v___y_3817_);
        crate::leanh::lean_inc_ref(v___y_3816_);
        crate::leanh::lean_inc(v___y_3815_);
        crate::leanh::lean_inc(v___y_3814_);
        crate::leanh::lean_inc_ref(v_d_3825_);
        v___x_3826_ = crate::leanh::lean_apply_8(
            v_f_3811_,
            v_d_3825_,
            v___y_3814_,
            v___y_3815_,
            v___y_3816_,
            v___y_3817_,
            v___y_3818_,
            v___y_3819_,
            crate::leanh::lean_box(0),
        );
        if crate::leanh::lean_obj_tag(v___x_3826_) == 0 {
            let mut v_v_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_3826_, 1);
            v_v_3827_ = lean_expr_instantiate_rev(v_value_3823_, v_fvars_3812_);
            crate::leanh::lean_dec_ref(v_value_3823_);
            crate::leanh::lean_inc_ref(v_f_3811_);
            crate::leanh::lean_inc(v___y_3819_);
            crate::leanh::lean_inc_ref(v___y_3818_);
            crate::leanh::lean_inc(v___y_3817_);
            crate::leanh::lean_inc_ref(v___y_3816_);
            crate::leanh::lean_inc(v___y_3815_);
            crate::leanh::lean_inc(v___y_3814_);
            crate::leanh::lean_inc_ref(v_v_3827_);
            v___x_3828_ = crate::leanh::lean_apply_8(
                v_f_3811_,
                v_v_3827_,
                v___y_3814_,
                v___y_3815_,
                v___y_3816_,
                v___y_3817_,
                v___y_3818_,
                v___y_3819_,
                crate::leanh::lean_box(0),
            );
            if crate::leanh::lean_obj_tag(v___x_3828_) == 0 {
                let mut v___f_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3830_: u8 = 0;
                let mut v___x_3831_: u8 = 0;
                let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref_known(v___x_3828_, 1);
                v___f_3829_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12___lam__0___boxed as *mut core::ffi::c_void, 11, 3);
                crate::leanh::lean_closure_set(v___f_3829_, 0, v_fvars_3812_);
                crate::leanh::lean_closure_set(v___f_3829_, 1, v_f_3811_);
                crate::leanh::lean_closure_set(v___f_3829_, 2, v_body_3824_);
                v___x_3830_ = 0;
                v___x_3831_ = 0;
                v___x_3832_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15___redArg(v_declName_3821_, v_d_3825_, v_v_3827_, v___f_3829_, v___x_3830_, v___x_3831_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
                return v___x_3832_;
            } else {
                crate::leanh::lean_dec_ref(v_v_3827_);
                crate::leanh::lean_dec_ref(v_d_3825_);
                crate::leanh::lean_dec_ref(v_body_3824_);
                crate::leanh::lean_dec(v_declName_3821_);
                crate::leanh::lean_dec_ref(v_fvars_3812_);
                crate::leanh::lean_dec_ref(v_f_3811_);
                return v___x_3828_;
            }
        } else {
            crate::leanh::lean_dec_ref(v_d_3825_);
            crate::leanh::lean_dec_ref(v_body_3824_);
            crate::leanh::lean_dec_ref(v_value_3823_);
            crate::leanh::lean_dec(v_declName_3821_);
            crate::leanh::lean_dec_ref(v_fvars_3812_);
            crate::leanh::lean_dec_ref(v_f_3811_);
            return v___x_3826_;
        }
    } else {
        let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3833_ = lean_expr_instantiate_rev(v_a_3813_, v_fvars_3812_);
        crate::leanh::lean_dec_ref(v_fvars_3812_);
        crate::leanh::lean_dec_ref(v_a_3813_);
        crate::leanh::lean_inc(v___y_3819_);
        crate::leanh::lean_inc_ref(v___y_3818_);
        crate::leanh::lean_inc(v___y_3817_);
        crate::leanh::lean_inc_ref(v___y_3816_);
        crate::leanh::lean_inc(v___y_3815_);
        crate::leanh::lean_inc(v___y_3814_);
        v___x_3834_ = crate::leanh::lean_apply_8(
            v_f_3811_,
            v___x_3833_,
            v___y_3814_,
            v___y_3815_,
            v___y_3816_,
            v___y_3817_,
            v___y_3818_,
            v___y_3819_,
            crate::leanh::lean_box(0),
        );
        return v___x_3834_;
    }
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12___lam__0(
    mut v_fvars_3835_: *mut crate::leanh::LeanObject,
    mut v_f_3836_: *mut crate::leanh::LeanObject,
    mut v_body_3837_: *mut crate::leanh::LeanObject,
    mut v_x_3838_: *mut crate::leanh::LeanObject,
    mut v___y_3839_: *mut crate::leanh::LeanObject,
    mut v___y_3840_: *mut crate::leanh::LeanObject,
    mut v___y_3841_: *mut crate::leanh::LeanObject,
    mut v___y_3842_: *mut crate::leanh::LeanObject,
    mut v___y_3843_: *mut crate::leanh::LeanObject,
    mut v___y_3844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3846_ = lean_array_push(v_fvars_3835_, v_x_3838_);
    v___x_3847_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12(v_f_3836_, v___x_3846_, v_body_3837_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_);
    return v___x_3847_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12___boxed(
    mut v_f_3848_: *mut crate::leanh::LeanObject,
    mut v_fvars_3849_: *mut crate::leanh::LeanObject,
    mut v_a_3850_: *mut crate::leanh::LeanObject,
    mut v___y_3851_: *mut crate::leanh::LeanObject,
    mut v___y_3852_: *mut crate::leanh::LeanObject,
    mut v___y_3853_: *mut crate::leanh::LeanObject,
    mut v___y_3854_: *mut crate::leanh::LeanObject,
    mut v___y_3855_: *mut crate::leanh::LeanObject,
    mut v___y_3856_: *mut crate::leanh::LeanObject,
    mut v___y_3857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3858_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12(v_f_3848_, v_fvars_3849_, v_a_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
    crate::leanh::lean_dec(v___y_3856_);
    crate::leanh::lean_dec_ref(v___y_3855_);
    crate::leanh::lean_dec(v___y_3854_);
    crate::leanh::lean_dec_ref(v___y_3853_);
    crate::leanh::lean_dec(v___y_3852_);
    crate::leanh::lean_dec(v___y_3851_);
    return v_res_3858_;
}
pub unsafe fn l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5(
    mut v_f_3859_: *mut crate::leanh::LeanObject,
    mut v_e_3860_: *mut crate::leanh::LeanObject,
    mut v___y_3861_: *mut crate::leanh::LeanObject,
    mut v___y_3862_: *mut crate::leanh::LeanObject,
    mut v___y_3863_: *mut crate::leanh::LeanObject,
    mut v___y_3864_: *mut crate::leanh::LeanObject,
    mut v___y_3865_: *mut crate::leanh::LeanObject,
    mut v___y_3866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3868_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3___closed__0;
    v___x_3869_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12(v_f_3859_, v___x_3868_, v_e_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_);
    return v___x_3869_;
}
pub unsafe fn l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5___boxed(
    mut v_f_3870_: *mut crate::leanh::LeanObject,
    mut v_e_3871_: *mut crate::leanh::LeanObject,
    mut v___y_3872_: *mut crate::leanh::LeanObject,
    mut v___y_3873_: *mut crate::leanh::LeanObject,
    mut v___y_3874_: *mut crate::leanh::LeanObject,
    mut v___y_3875_: *mut crate::leanh::LeanObject,
    mut v___y_3876_: *mut crate::leanh::LeanObject,
    mut v___y_3877_: *mut crate::leanh::LeanObject,
    mut v___y_3878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3879_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5(v_f_3870_, v_e_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_);
    crate::leanh::lean_dec(v___y_3877_);
    crate::leanh::lean_dec_ref(v___y_3876_);
    crate::leanh::lean_dec(v___y_3875_);
    crate::leanh::lean_dec_ref(v___y_3874_);
    crate::leanh::lean_dec(v___y_3873_);
    crate::leanh::lean_dec(v___y_3872_);
    return v_res_3879_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10___lam__0___boxed(
    mut v_fvars_3880_: *mut crate::leanh::LeanObject,
    mut v_f_3881_: *mut crate::leanh::LeanObject,
    mut v_body_3882_: *mut crate::leanh::LeanObject,
    mut v_x_3883_: *mut crate::leanh::LeanObject,
    mut v___y_3884_: *mut crate::leanh::LeanObject,
    mut v___y_3885_: *mut crate::leanh::LeanObject,
    mut v___y_3886_: *mut crate::leanh::LeanObject,
    mut v___y_3887_: *mut crate::leanh::LeanObject,
    mut v___y_3888_: *mut crate::leanh::LeanObject,
    mut v___y_3889_: *mut crate::leanh::LeanObject,
    mut v___y_3890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3891_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10___lam__0(v_fvars_3880_, v_f_3881_, v_body_3882_, v_x_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_);
    crate::leanh::lean_dec(v___y_3889_);
    crate::leanh::lean_dec_ref(v___y_3888_);
    crate::leanh::lean_dec(v___y_3887_);
    crate::leanh::lean_dec_ref(v___y_3886_);
    crate::leanh::lean_dec(v___y_3885_);
    crate::leanh::lean_dec(v___y_3884_);
    return v_res_3891_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10(
    mut v_f_3892_: *mut crate::leanh::LeanObject,
    mut v_fvars_3893_: *mut crate::leanh::LeanObject,
    mut v_a_3894_: *mut crate::leanh::LeanObject,
    mut v___y_3895_: *mut crate::leanh::LeanObject,
    mut v___y_3896_: *mut crate::leanh::LeanObject,
    mut v___y_3897_: *mut crate::leanh::LeanObject,
    mut v___y_3898_: *mut crate::leanh::LeanObject,
    mut v___y_3899_: *mut crate::leanh::LeanObject,
    mut v___y_3900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_a_3894_) == 6 {
        let mut v_binderName_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderType_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_3905_: u8 = 0;
        let mut v_d_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_binderName_3902_ = crate::leanh::lean_ctor_get(v_a_3894_, 0);
        crate::leanh::lean_inc(v_binderName_3902_);
        v_binderType_3903_ = crate::leanh::lean_ctor_get(v_a_3894_, 1);
        crate::leanh::lean_inc_ref(v_binderType_3903_);
        v_body_3904_ = crate::leanh::lean_ctor_get(v_a_3894_, 2);
        crate::leanh::lean_inc_ref(v_body_3904_);
        v_binderInfo_3905_ = crate::leanh::lean_ctor_get_uint8(
            v_a_3894_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        );
        crate::leanh::lean_dec_ref_known(v_a_3894_, 3);
        v_d_3906_ = lean_expr_instantiate_rev(v_binderType_3903_, v_fvars_3893_);
        crate::leanh::lean_dec_ref(v_binderType_3903_);
        crate::leanh::lean_inc_ref(v_f_3892_);
        crate::leanh::lean_inc(v___y_3900_);
        crate::leanh::lean_inc_ref(v___y_3899_);
        crate::leanh::lean_inc(v___y_3898_);
        crate::leanh::lean_inc_ref(v___y_3897_);
        crate::leanh::lean_inc(v___y_3896_);
        crate::leanh::lean_inc(v___y_3895_);
        crate::leanh::lean_inc_ref(v_d_3906_);
        v___x_3907_ = crate::leanh::lean_apply_8(
            v_f_3892_,
            v_d_3906_,
            v___y_3895_,
            v___y_3896_,
            v___y_3897_,
            v___y_3898_,
            v___y_3899_,
            v___y_3900_,
            crate::leanh::lean_box(0),
        );
        if crate::leanh::lean_obj_tag(v___x_3907_) == 0 {
            let mut v___f_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3909_: u8 = 0;
            let mut v___x_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_3907_, 1);
            v___f_3908_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10___lam__0___boxed as *mut core::ffi::c_void, 11, 3);
            crate::leanh::lean_closure_set(v___f_3908_, 0, v_fvars_3893_);
            crate::leanh::lean_closure_set(v___f_3908_, 1, v_f_3892_);
            crate::leanh::lean_closure_set(v___f_3908_, 2, v_body_3904_);
            v___x_3909_ = 0;
            v___x_3910_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_binderName_3902_, v_binderInfo_3905_, v_d_3906_, v___f_3908_, v___x_3909_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
            return v___x_3910_;
        } else {
            crate::leanh::lean_dec_ref(v_d_3906_);
            crate::leanh::lean_dec_ref(v_body_3904_);
            crate::leanh::lean_dec(v_binderName_3902_);
            crate::leanh::lean_dec_ref(v_fvars_3893_);
            crate::leanh::lean_dec_ref(v_f_3892_);
            return v___x_3907_;
        }
    } else {
        let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3911_ = lean_expr_instantiate_rev(v_a_3894_, v_fvars_3893_);
        crate::leanh::lean_dec_ref(v_fvars_3893_);
        crate::leanh::lean_dec_ref(v_a_3894_);
        crate::leanh::lean_inc(v___y_3900_);
        crate::leanh::lean_inc_ref(v___y_3899_);
        crate::leanh::lean_inc(v___y_3898_);
        crate::leanh::lean_inc_ref(v___y_3897_);
        crate::leanh::lean_inc(v___y_3896_);
        crate::leanh::lean_inc(v___y_3895_);
        v___x_3912_ = crate::leanh::lean_apply_8(
            v_f_3892_,
            v___x_3911_,
            v___y_3895_,
            v___y_3896_,
            v___y_3897_,
            v___y_3898_,
            v___y_3899_,
            v___y_3900_,
            crate::leanh::lean_box(0),
        );
        return v___x_3912_;
    }
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10___lam__0(
    mut v_fvars_3913_: *mut crate::leanh::LeanObject,
    mut v_f_3914_: *mut crate::leanh::LeanObject,
    mut v_body_3915_: *mut crate::leanh::LeanObject,
    mut v_x_3916_: *mut crate::leanh::LeanObject,
    mut v___y_3917_: *mut crate::leanh::LeanObject,
    mut v___y_3918_: *mut crate::leanh::LeanObject,
    mut v___y_3919_: *mut crate::leanh::LeanObject,
    mut v___y_3920_: *mut crate::leanh::LeanObject,
    mut v___y_3921_: *mut crate::leanh::LeanObject,
    mut v___y_3922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3924_ = lean_array_push(v_fvars_3913_, v_x_3916_);
    v___x_3925_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10(v_f_3914_, v___x_3924_, v_body_3915_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_);
    return v___x_3925_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10___boxed(
    mut v_f_3926_: *mut crate::leanh::LeanObject,
    mut v_fvars_3927_: *mut crate::leanh::LeanObject,
    mut v_a_3928_: *mut crate::leanh::LeanObject,
    mut v___y_3929_: *mut crate::leanh::LeanObject,
    mut v___y_3930_: *mut crate::leanh::LeanObject,
    mut v___y_3931_: *mut crate::leanh::LeanObject,
    mut v___y_3932_: *mut crate::leanh::LeanObject,
    mut v___y_3933_: *mut crate::leanh::LeanObject,
    mut v___y_3934_: *mut crate::leanh::LeanObject,
    mut v___y_3935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3936_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10(v_f_3926_, v_fvars_3927_, v_a_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_);
    crate::leanh::lean_dec(v___y_3934_);
    crate::leanh::lean_dec_ref(v___y_3933_);
    crate::leanh::lean_dec(v___y_3932_);
    crate::leanh::lean_dec_ref(v___y_3931_);
    crate::leanh::lean_dec(v___y_3930_);
    crate::leanh::lean_dec(v___y_3929_);
    return v_res_3936_;
}
pub unsafe fn l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4(
    mut v_f_3937_: *mut crate::leanh::LeanObject,
    mut v_e_3938_: *mut crate::leanh::LeanObject,
    mut v___y_3939_: *mut crate::leanh::LeanObject,
    mut v___y_3940_: *mut crate::leanh::LeanObject,
    mut v___y_3941_: *mut crate::leanh::LeanObject,
    mut v___y_3942_: *mut crate::leanh::LeanObject,
    mut v___y_3943_: *mut crate::leanh::LeanObject,
    mut v___y_3944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3946_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3___closed__0;
    v___x_3947_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4_spec__10(v_f_3937_, v___x_3946_, v_e_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_);
    return v___x_3947_;
}
pub unsafe fn l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4___boxed(
    mut v_f_3948_: *mut crate::leanh::LeanObject,
    mut v_e_3949_: *mut crate::leanh::LeanObject,
    mut v___y_3950_: *mut crate::leanh::LeanObject,
    mut v___y_3951_: *mut crate::leanh::LeanObject,
    mut v___y_3952_: *mut crate::leanh::LeanObject,
    mut v___y_3953_: *mut crate::leanh::LeanObject,
    mut v___y_3954_: *mut crate::leanh::LeanObject,
    mut v___y_3955_: *mut crate::leanh::LeanObject,
    mut v___y_3956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3957_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4(v_f_3948_, v_e_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
    crate::leanh::lean_dec(v___y_3955_);
    crate::leanh::lean_dec_ref(v___y_3954_);
    crate::leanh::lean_dec(v___y_3953_);
    crate::leanh::lean_dec_ref(v___y_3952_);
    crate::leanh::lean_dec(v___y_3951_);
    crate::leanh::lean_dec(v___y_3950_);
    return v_res_3957_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_a_3958_: *mut crate::leanh::LeanObject,
    mut v_x_3959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: u8 = 0;
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3959_) == 0 {
                    v___x_3960_ = crate::leanh::lean_box(0);
                    return v___x_3960_;
                } else {
                    v_key_3961_ = crate::leanh::lean_ctor_get(v_x_3959_, 0);
                    v_value_3962_ = crate::leanh::lean_ctor_get(v_x_3959_, 1);
                    v_tail_3963_ = crate::leanh::lean_ctor_get(v_x_3959_, 2);
                    v___x_3964_ = lean_expr_eqv(v_key_3961_, v_a_3958_);
                    if v___x_3964_ == 0 {
                        v_x_3959_ = v_tail_3963_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_3962_);
                        v___x_3966_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3966_, 0, v_value_3962_);
                        return v___x_3966_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_a_3967_: *mut crate::leanh::LeanObject,
    mut v_x_3968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3969_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2___redArg(v_a_3967_, v_x_3968_);
    crate::leanh::lean_dec(v_x_3968_);
    crate::leanh::lean_dec_ref(v_a_3967_);
    return v_res_3969_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1___redArg(
    mut v_m_3970_: *mut crate::leanh::LeanObject,
    mut v_a_3971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: u64 = 0;
    let mut v___x_3975_: u64 = 0;
    let mut v___x_3976_: u64 = 0;
    let mut v_fold_3977_: u64 = 0;
    let mut v___x_3978_: u64 = 0;
    let mut v___x_3979_: u64 = 0;
    let mut v___x_3980_: u64 = 0;
    let mut v___x_3981_: usize = 0;
    let mut v___x_3982_: usize = 0;
    let mut v___x_3983_: usize = 0;
    let mut v___x_3984_: usize = 0;
    let mut v___x_3985_: usize = 0;
    let mut v___x_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3972_ = crate::leanh::lean_ctor_get(v_m_3970_, 1);
    v___x_3973_ = lean_array_get_size(v_buckets_3972_);
    v___x_3974_ = l_Lean_Expr_hash(v_a_3971_);
    v___x_3975_ = 32u64;
    v___x_3976_ = lean_uint64_shift_right(v___x_3974_, v___x_3975_);
    v_fold_3977_ = lean_uint64_xor(v___x_3974_, v___x_3976_);
    v___x_3978_ = 16u64;
    v___x_3979_ = lean_uint64_shift_right(v_fold_3977_, v___x_3978_);
    v___x_3980_ = lean_uint64_xor(v_fold_3977_, v___x_3979_);
    v___x_3981_ = lean_uint64_to_usize(v___x_3980_);
    v___x_3982_ = lean_usize_of_nat(v___x_3973_);
    v___x_3983_ = 1usize;
    v___x_3984_ = lean_usize_sub(v___x_3982_, v___x_3983_);
    v___x_3985_ = lean_usize_land(v___x_3981_, v___x_3984_);
    v___x_3986_ = lean_array_uget_borrowed(v_buckets_3972_, v___x_3985_);
    v___x_3987_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2___redArg(v_a_3971_, v___x_3986_);
    return v___x_3987_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_m_3988_: *mut crate::leanh::LeanObject,
    mut v_a_3989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3990_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1___redArg(v_m_3988_, v_a_3989_);
    crate::leanh::lean_dec_ref(v_a_3989_);
    crate::leanh::lean_dec_ref(v_m_3988_);
    return v_res_3990_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__0(
    mut v_00_u03b1_3991_: *mut crate::leanh::LeanObject,
    mut v_x_3992_: *mut crate::leanh::LeanObject,
    mut v___y_3993_: *mut crate::leanh::LeanObject,
    mut v___y_3994_: *mut crate::leanh::LeanObject,
    mut v___y_3995_: *mut crate::leanh::LeanObject,
    mut v___y_3996_: *mut crate::leanh::LeanObject,
    mut v___y_3997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3999_ = crate::leanh::lean_apply_1(v_x_3992_, crate::leanh::lean_box(0));
    v___x_4000_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4000_, 0, v___x_3999_);
    return v___x_4000_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__0___boxed(
    mut v_00_u03b1_4001_: *mut crate::leanh::LeanObject,
    mut v_x_4002_: *mut crate::leanh::LeanObject,
    mut v___y_4003_: *mut crate::leanh::LeanObject,
    mut v___y_4004_: *mut crate::leanh::LeanObject,
    mut v___y_4005_: *mut crate::leanh::LeanObject,
    mut v___y_4006_: *mut crate::leanh::LeanObject,
    mut v___y_4007_: *mut crate::leanh::LeanObject,
    mut v___y_4008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4009_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__0(v_00_u03b1_4001_, v_x_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_);
    crate::leanh::lean_dec(v___y_4007_);
    crate::leanh::lean_dec_ref(v___y_4006_);
    crate::leanh::lean_dec(v___y_4005_);
    crate::leanh::lean_dec_ref(v___y_4004_);
    crate::leanh::lean_dec(v___y_4003_);
    return v_res_4009_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___boxed(
    mut v_fn_4010_: *mut crate::leanh::LeanObject,
    mut v_e_4011_: *mut crate::leanh::LeanObject,
    mut v_a_4012_: *mut crate::leanh::LeanObject,
    mut v___y_4013_: *mut crate::leanh::LeanObject,
    mut v___y_4014_: *mut crate::leanh::LeanObject,
    mut v___y_4015_: *mut crate::leanh::LeanObject,
    mut v___y_4016_: *mut crate::leanh::LeanObject,
    mut v___y_4017_: *mut crate::leanh::LeanObject,
    mut v___y_4018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4019_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0(v_fn_4010_, v_e_4011_, v_a_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_);
    crate::leanh::lean_dec(v___y_4017_);
    crate::leanh::lean_dec_ref(v___y_4016_);
    crate::leanh::lean_dec(v___y_4015_);
    crate::leanh::lean_dec_ref(v___y_4014_);
    crate::leanh::lean_dec(v___y_4013_);
    crate::leanh::lean_dec(v_a_4012_);
    return v_res_4019_;
}
pub unsafe fn l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0(
    mut v_fn_4020_: *mut crate::leanh::LeanObject,
    mut v_e_4021_: *mut crate::leanh::LeanObject,
    mut v_a_4022_: *mut crate::leanh::LeanObject,
    mut v___y_4023_: *mut crate::leanh::LeanObject,
    mut v___y_4024_: *mut crate::leanh::LeanObject,
    mut v___y_4025_: *mut crate::leanh::LeanObject,
    mut v___y_4026_: *mut crate::leanh::LeanObject,
    mut v___y_4027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4035_: u8 = 0;
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4039_: u8 = 0;
    let mut v_unused_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4049_: u8 = 0;
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: u8 = 0;
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4073_: u8 = 0;
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4077_: u8 = 0;
    let mut v_val_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4082_: u8 = 0;
    let mut v_a_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4086_: u8 = 0;
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4090_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_4022_);
                v___x_4044_ = crate::leanh::lean_alloc_closure(
                    l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___x_4044_, 0, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4044_, 1, crate::leanh::lean_box(0));
                crate::leanh::lean_closure_set(v___x_4044_, 2, v_a_4022_);
                v___x_4045_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__0(crate::leanh::lean_box(0), v___x_4044_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
                if crate::leanh::lean_obj_tag(v___x_4045_) == 0 {
                    v_a_4046_ = crate::leanh::lean_ctor_get(v___x_4045_, 0);
                    v_isSharedCheck_4082_ = (!crate::leanh::lean_is_exclusive(v___x_4045_)) as u8;
                    if v_isSharedCheck_4082_ == 0 {
                        v___x_4048_ = v___x_4045_;
                        v_isShared_4049_ = v_isSharedCheck_4082_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4046_);
                        crate::leanh::lean_dec(v___x_4045_);
                        v___x_4048_ = crate::leanh::lean_box(0);
                        v_isShared_4049_ = v_isSharedCheck_4082_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_4021_);
                    crate::leanh::lean_dec_ref(v_fn_4020_);
                    v_a_4083_ = crate::leanh::lean_ctor_get(v___x_4045_, 0);
                    v_isSharedCheck_4090_ = (!crate::leanh::lean_is_exclusive(v___x_4045_)) as u8;
                    if v_isSharedCheck_4090_ == 0 {
                        v___x_4085_ = v___x_4045_;
                        v_isShared_4086_ = v_isSharedCheck_4090_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4083_);
                        crate::leanh::lean_dec(v___x_4045_);
                        v___x_4085_ = crate::leanh::lean_box(0);
                        v_isShared_4086_ = v_isSharedCheck_4090_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_4022_);
                v___f_4031_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__1___boxed as *mut core::ffi::c_void, 4, 3);
                crate::leanh::lean_closure_set(v___f_4031_, 0, v_a_4022_);
                crate::leanh::lean_closure_set(v___f_4031_, 1, v_e_4021_);
                crate::leanh::lean_closure_set(v___f_4031_, 2, v_a_4030_);
                v___x_4032_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___lam__0(crate::leanh::lean_box(0), v___f_4031_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
                if crate::leanh::lean_obj_tag(v___x_4032_) == 0 {
                    v_isSharedCheck_4039_ = (!crate::leanh::lean_is_exclusive(v___x_4032_)) as u8;
                    if v_isSharedCheck_4039_ == 0 {
                        v_unused_4040_ = crate::leanh::lean_ctor_get(v___x_4032_, 0);
                        crate::leanh::lean_dec(v_unused_4040_);
                        v___x_4034_ = v___x_4032_;
                        v_isShared_4035_ = v_isSharedCheck_4039_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4032_);
                        v___x_4034_ = crate::leanh::lean_box(0);
                        v_isShared_4035_ = v_isSharedCheck_4039_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_4032_;
                }
            }
            2 => {
                if v_isShared_4035_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4034_, 0, v_a_4030_);
                    v___x_4037_ = v___x_4034_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4038_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4038_, 0, v_a_4030_);
                    v___x_4037_ = v_reuseFailAlloc_4038_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4037_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v___y_4042_) == 0 {
                    v_a_4043_ = crate::leanh::lean_ctor_get(v___y_4042_, 0);
                    crate::leanh::lean_inc(v_a_4043_);
                    crate::leanh::lean_dec_ref_known(v___y_4042_, 1);
                    v_a_4030_ = v_a_4043_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_e_4021_);
                    return v___y_4042_;
                }
            }
            5 => {
                v___x_4050_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1___redArg(v_a_4046_, v_e_4021_);
                crate::leanh::lean_dec(v_a_4046_);
                if crate::leanh::lean_obj_tag(v___x_4050_) == 0 {
                    crate::leanh::lean_del_object(v___x_4048_);
                    crate::leanh::lean_inc_ref(v_fn_4020_);
                    crate::leanh::lean_inc(v___y_4027_);
                    crate::leanh::lean_inc_ref(v___y_4026_);
                    crate::leanh::lean_inc(v___y_4025_);
                    crate::leanh::lean_inc_ref(v___y_4024_);
                    crate::leanh::lean_inc(v___y_4023_);
                    crate::leanh::lean_inc_ref(v_e_4021_);
                    v___x_4051_ = crate::leanh::lean_apply_7(
                        v_fn_4020_,
                        v_e_4021_,
                        v___y_4023_,
                        v___y_4024_,
                        v___y_4025_,
                        v___y_4026_,
                        v___y_4027_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_4051_) == 0 {
                        v_a_4052_ = crate::leanh::lean_ctor_get(v___x_4051_, 0);
                        crate::leanh::lean_inc(v_a_4052_);
                        crate::leanh::lean_dec_ref_known(v___x_4051_, 1);
                        v___x_4053_ = (crate::leanh::lean_unbox(v_a_4052_) as u8);
                        crate::leanh::lean_dec(v_a_4052_);
                        if v___x_4053_ == 0 {
                            crate::leanh::lean_dec_ref(v_fn_4020_);
                            v___x_4054_ = crate::leanh::lean_box(0);
                            v_a_4030_ = v___x_4054_;
                            state = 1;
                            continue;
                        } else {
                            match crate::leanh::lean_obj_tag(v_e_4021_) {
                                7 => {
                                    v___x_4055_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___boxed as *mut core::ffi::c_void, 9, 1);
                                    crate::leanh::lean_closure_set(v___x_4055_, 0, v_fn_4020_);
                                    crate::leanh::lean_inc_ref(v_e_4021_);
                                    v___x_4056_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3(v___x_4055_, v_e_4021_, v_a_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
                                    v___y_4042_ = v___x_4056_;
                                    state = 4;
                                    continue;
                                }
                                6 => {
                                    v___x_4057_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___boxed as *mut core::ffi::c_void, 9, 1);
                                    crate::leanh::lean_closure_set(v___x_4057_, 0, v_fn_4020_);
                                    crate::leanh::lean_inc_ref(v_e_4021_);
                                    v___x_4058_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__4(v___x_4057_, v_e_4021_, v_a_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
                                    v___y_4042_ = v___x_4058_;
                                    state = 4;
                                    continue;
                                }
                                8 => {
                                    v___x_4059_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0___boxed as *mut core::ffi::c_void, 9, 1);
                                    crate::leanh::lean_closure_set(v___x_4059_, 0, v_fn_4020_);
                                    crate::leanh::lean_inc_ref(v_e_4021_);
                                    v___x_4060_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5(v___x_4059_, v_e_4021_, v_a_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
                                    v___y_4042_ = v___x_4060_;
                                    state = 4;
                                    continue;
                                }
                                5 => {
                                    v_fn_4061_ = crate::leanh::lean_ctor_get(v_e_4021_, 0);
                                    v_arg_4062_ = crate::leanh::lean_ctor_get(v_e_4021_, 1);
                                    crate::leanh::lean_inc_ref(v_fn_4061_);
                                    crate::leanh::lean_inc_ref(v_fn_4020_);
                                    v___x_4063_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0(v_fn_4020_, v_fn_4061_, v_a_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
                                    if crate::leanh::lean_obj_tag(v___x_4063_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_4063_, 1);
                                        crate::leanh::lean_inc_ref(v_arg_4062_);
                                        v___x_4064_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0(v_fn_4020_, v_arg_4062_, v_a_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
                                        v___y_4042_ = v___x_4064_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec_ref(v_fn_4020_);
                                        v___y_4042_ = v___x_4063_;
                                        state = 4;
                                        continue;
                                    }
                                }
                                10 => {
                                    v_expr_4065_ = crate::leanh::lean_ctor_get(v_e_4021_, 1);
                                    crate::leanh::lean_inc_ref(v_expr_4065_);
                                    v___x_4066_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0(v_fn_4020_, v_expr_4065_, v_a_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
                                    v___y_4042_ = v___x_4066_;
                                    state = 4;
                                    continue;
                                }
                                11 => {
                                    v_struct_4067_ = crate::leanh::lean_ctor_get(v_e_4021_, 2);
                                    crate::leanh::lean_inc_ref(v_struct_4067_);
                                    v___x_4068_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0(v_fn_4020_, v_struct_4067_, v_a_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
                                    v___y_4042_ = v___x_4068_;
                                    state = 4;
                                    continue;
                                }
                                _ => {
                                    crate::leanh::lean_dec_ref(v_fn_4020_);
                                    v___x_4069_ = crate::leanh::lean_box(0);
                                    v_a_4030_ = v___x_4069_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_4021_);
                        crate::leanh::lean_dec_ref(v_fn_4020_);
                        v_a_4070_ = crate::leanh::lean_ctor_get(v___x_4051_, 0);
                        v_isSharedCheck_4077_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4051_)) as u8;
                        if v_isSharedCheck_4077_ == 0 {
                            v___x_4072_ = v___x_4051_;
                            v_isShared_4073_ = v_isSharedCheck_4077_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4070_);
                            crate::leanh::lean_dec(v___x_4051_);
                            v___x_4072_ = crate::leanh::lean_box(0);
                            v_isShared_4073_ = v_isSharedCheck_4077_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_4021_);
                    crate::leanh::lean_dec_ref(v_fn_4020_);
                    v_val_4078_ = crate::leanh::lean_ctor_get(v___x_4050_, 0);
                    crate::leanh::lean_inc(v_val_4078_);
                    crate::leanh::lean_dec_ref_known(v___x_4050_, 1);
                    if v_isShared_4049_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4048_, 0, v_val_4078_);
                        v___x_4080_ = v___x_4048_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4081_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4081_, 0, v_val_4078_);
                        v___x_4080_ = v_reuseFailAlloc_4081_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_4073_ == 0 {
                    v___x_4075_ = v___x_4072_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4076_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_a_4070_);
                    v___x_4075_ = v_reuseFailAlloc_4076_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4075_;
            }
            8 => {
                return v___x_4080_;
            }
            9 => {
                if v_isShared_4086_ == 0 {
                    v___x_4088_ = v___x_4085_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4089_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_a_4083_);
                    v___x_4088_ = v_reuseFailAlloc_4089_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4088_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4091_ = crate::leanh::lean_box(0);
    v___x_4092_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_4093_ = lean_mk_array(v___x_4092_, v___x_4091_);
    return v___x_4093_;
}
pub unsafe fn _init_l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4094_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__0_once), _init_l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__0);
    v___x_4095_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4096_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4096_, 0, v___x_4095_);
    crate::leanh::lean_ctor_set(v___x_4096_, 1, v___x_4094_);
    return v___x_4096_;
}
pub unsafe fn _init_l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4097_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__1_once), _init_l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__1);
    v___x_4098_ =
        crate::leanh::lean_alloc_closure(l_ST_Prim_mkRef___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_4098_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4098_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_4098_, 2, v___x_4097_);
    return v___x_4098_;
}
pub unsafe fn l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0(
    mut v_input_4099_: *mut crate::leanh::LeanObject,
    mut v_fn_4100_: *mut crate::leanh::LeanObject,
    mut v___y_4101_: *mut crate::leanh::LeanObject,
    mut v___y_4102_: *mut crate::leanh::LeanObject,
    mut v___y_4103_: *mut crate::leanh::LeanObject,
    mut v___y_4104_: *mut crate::leanh::LeanObject,
    mut v___y_4105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4116_: u8 = 0;
    let mut v___x_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4120_: u8 = 0;
    let mut v_unused_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4107_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__2_once), _init_l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___closed__2);
                v___x_4108_ = l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___lam__0(crate::leanh::lean_box(0), v___x_4107_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_);
                v_a_4109_ = crate::leanh::lean_ctor_get(v___x_4108_, 0);
                crate::leanh::lean_inc(v_a_4109_);
                crate::leanh::lean_dec_ref(v___x_4108_);
                v___x_4110_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0(v_fn_4100_, v_input_4099_, v_a_4109_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_);
                if crate::leanh::lean_obj_tag(v___x_4110_) == 0 {
                    v_a_4111_ = crate::leanh::lean_ctor_get(v___x_4110_, 0);
                    crate::leanh::lean_inc(v_a_4111_);
                    crate::leanh::lean_dec_ref_known(v___x_4110_, 1);
                    v___x_4112_ = crate::leanh::lean_alloc_closure(
                        l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___x_4112_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_4112_, 1, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_4112_, 2, v_a_4109_);
                    v___x_4113_ = l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___lam__0(crate::leanh::lean_box(0), v___x_4112_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_);
                    v_isSharedCheck_4120_ = (!crate::leanh::lean_is_exclusive(v___x_4113_)) as u8;
                    if v_isSharedCheck_4120_ == 0 {
                        v_unused_4121_ = crate::leanh::lean_ctor_get(v___x_4113_, 0);
                        crate::leanh::lean_dec(v_unused_4121_);
                        v___x_4115_ = v___x_4113_;
                        v_isShared_4116_ = v_isSharedCheck_4120_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4113_);
                        v___x_4115_ = crate::leanh::lean_box(0);
                        v_isShared_4116_ = v_isSharedCheck_4120_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4109_);
                    return v___x_4110_;
                }
            }
            1 => {
                if v_isShared_4116_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4115_, 0, v_a_4111_);
                    v___x_4118_ = v___x_4115_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4119_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4119_, 0, v_a_4111_);
                    v___x_4118_ = v_reuseFailAlloc_4119_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4118_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0___boxed(
    mut v_input_4122_: *mut crate::leanh::LeanObject,
    mut v_fn_4123_: *mut crate::leanh::LeanObject,
    mut v___y_4124_: *mut crate::leanh::LeanObject,
    mut v___y_4125_: *mut crate::leanh::LeanObject,
    mut v___y_4126_: *mut crate::leanh::LeanObject,
    mut v___y_4127_: *mut crate::leanh::LeanObject,
    mut v___y_4128_: *mut crate::leanh::LeanObject,
    mut v___y_4129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4130_ = l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0(v_input_4122_, v_fn_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
    crate::leanh::lean_dec(v___y_4128_);
    crate::leanh::lean_dec_ref(v___y_4127_);
    crate::leanh::lean_dec(v___y_4126_);
    crate::leanh::lean_dec_ref(v___y_4125_);
    crate::leanh::lean_dec(v___y_4124_);
    return v_res_4130_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs(
    mut v_e_4132_: *mut crate::leanh::LeanObject,
    mut v_a_4133_: *mut crate::leanh::LeanObject,
    mut v_a_4134_: *mut crate::leanh::LeanObject,
    mut v_a_4135_: *mut crate::leanh::LeanObject,
    mut v_a_4136_: *mut crate::leanh::LeanObject,
    mut v_a_4137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4139_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___closed__0;
    v___x_4140_ = l_Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0(v_e_4132_, v___f_4139_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_);
    return v___x_4140_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs___boxed(
    mut v_e_4141_: *mut crate::leanh::LeanObject,
    mut v_a_4142_: *mut crate::leanh::LeanObject,
    mut v_a_4143_: *mut crate::leanh::LeanObject,
    mut v_a_4144_: *mut crate::leanh::LeanObject,
    mut v_a_4145_: *mut crate::leanh::LeanObject,
    mut v_a_4146_: *mut crate::leanh::LeanObject,
    mut v_a_4147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4148_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs(v_e_4141_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_, v_a_4146_);
    crate::leanh::lean_dec(v_a_4146_);
    crate::leanh::lean_dec_ref(v_a_4145_);
    crate::leanh::lean_dec(v_a_4144_);
    crate::leanh::lean_dec_ref(v_a_4143_);
    crate::leanh::lean_dec(v_a_4142_);
    return v_res_4148_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4149_: *mut crate::leanh::LeanObject,
    mut v_m_4150_: *mut crate::leanh::LeanObject,
    mut v_a_4151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4152_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1___redArg(v_m_4150_, v_a_4151_);
    return v___x_4152_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4153_: *mut crate::leanh::LeanObject,
    mut v_m_4154_: *mut crate::leanh::LeanObject,
    mut v_a_4155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4156_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1(v_00_u03b2_4153_, v_m_4154_, v_a_4155_);
    crate::leanh::lean_dec_ref(v_a_4155_);
    crate::leanh::lean_dec_ref(v_m_4154_);
    return v_res_4156_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2(
    mut v_00_u03b2_4157_: *mut crate::leanh::LeanObject,
    mut v_m_4158_: *mut crate::leanh::LeanObject,
    mut v_a_4159_: *mut crate::leanh::LeanObject,
    mut v_b_4160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4161_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2___redArg(v_m_4158_, v_a_4159_, v_b_4160_);
    return v___x_4161_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_4162_: *mut crate::leanh::LeanObject,
    mut v_a_4163_: *mut crate::leanh::LeanObject,
    mut v_x_4164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4165_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2___redArg(v_a_4163_, v_x_4164_);
    return v___x_4165_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b2_4166_: *mut crate::leanh::LeanObject,
    mut v_a_4167_: *mut crate::leanh::LeanObject,
    mut v_x_4168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4169_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_4166_, v_a_4167_, v_x_4168_);
    crate::leanh::lean_dec(v_x_4168_);
    crate::leanh::lean_dec_ref(v_a_4167_);
    return v_res_4169_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4(
    mut v_00_u03b2_4170_: *mut crate::leanh::LeanObject,
    mut v_a_4171_: *mut crate::leanh::LeanObject,
    mut v_x_4172_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4173_: u8 = 0;
    v___x_4173_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4___redArg(v_a_4171_, v_x_4172_);
    return v___x_4173_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_00_u03b2_4174_: *mut crate::leanh::LeanObject,
    mut v_a_4175_: *mut crate::leanh::LeanObject,
    mut v_x_4176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4177_: u8 = 0;
    let mut v_r_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4177_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_4174_, v_a_4175_, v_x_4176_);
    crate::leanh::lean_dec(v_x_4176_);
    crate::leanh::lean_dec_ref(v_a_4175_);
    v_r_4178_ = crate::leanh::lean_box((v_res_4177_) as usize);
    return v_r_4178_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5(
    mut v_00_u03b2_4179_: *mut crate::leanh::LeanObject,
    mut v_data_4180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4181_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5___redArg(v_data_4180_);
    return v___x_4181_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__6(
    mut v_00_u03b2_4182_: *mut crate::leanh::LeanObject,
    mut v_a_4183_: *mut crate::leanh::LeanObject,
    mut v_b_4184_: *mut crate::leanh::LeanObject,
    mut v_x_4185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4186_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__6___redArg(v_a_4183_, v_b_4184_, v_x_4185_);
    return v___x_4186_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10(
    mut v_00_u03b1_4187_: *mut crate::leanh::LeanObject,
    mut v_name_4188_: *mut crate::leanh::LeanObject,
    mut v_bi_4189_: u8,
    mut v_type_4190_: *mut crate::leanh::LeanObject,
    mut v_k_4191_: *mut crate::leanh::LeanObject,
    mut v_kind_4192_: u8,
    mut v___y_4193_: *mut crate::leanh::LeanObject,
    mut v___y_4194_: *mut crate::leanh::LeanObject,
    mut v___y_4195_: *mut crate::leanh::LeanObject,
    mut v___y_4196_: *mut crate::leanh::LeanObject,
    mut v___y_4197_: *mut crate::leanh::LeanObject,
    mut v___y_4198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4200_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___redArg(v_name_4188_, v_bi_4189_, v_type_4190_, v_k_4191_, v_kind_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_);
    return v___x_4200_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10___boxed(
    mut v_00_u03b1_4201_: *mut crate::leanh::LeanObject,
    mut v_name_4202_: *mut crate::leanh::LeanObject,
    mut v_bi_4203_: *mut crate::leanh::LeanObject,
    mut v_type_4204_: *mut crate::leanh::LeanObject,
    mut v_k_4205_: *mut crate::leanh::LeanObject,
    mut v_kind_4206_: *mut crate::leanh::LeanObject,
    mut v___y_4207_: *mut crate::leanh::LeanObject,
    mut v___y_4208_: *mut crate::leanh::LeanObject,
    mut v___y_4209_: *mut crate::leanh::LeanObject,
    mut v___y_4210_: *mut crate::leanh::LeanObject,
    mut v___y_4211_: *mut crate::leanh::LeanObject,
    mut v___y_4212_: *mut crate::leanh::LeanObject,
    mut v___y_4213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_4214_: u8 = 0;
    let mut v_kind_boxed_4215_: u8 = 0;
    let mut v_res_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_4214_ = (crate::leanh::lean_unbox(v_bi_4203_) as u8);
    v_kind_boxed_4215_ = (crate::leanh::lean_unbox(v_kind_4206_) as u8);
    v_res_4216_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__3_spec__8_spec__10(v_00_u03b1_4201_, v_name_4202_, v_bi_boxed_4214_, v_type_4204_, v_k_4205_, v_kind_boxed_4215_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_);
    crate::leanh::lean_dec(v___y_4212_);
    crate::leanh::lean_dec_ref(v___y_4211_);
    crate::leanh::lean_dec(v___y_4210_);
    crate::leanh::lean_dec_ref(v___y_4209_);
    crate::leanh::lean_dec(v___y_4208_);
    crate::leanh::lean_dec(v___y_4207_);
    return v_res_4216_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15(
    mut v_00_u03b1_4217_: *mut crate::leanh::LeanObject,
    mut v_name_4218_: *mut crate::leanh::LeanObject,
    mut v_type_4219_: *mut crate::leanh::LeanObject,
    mut v_val_4220_: *mut crate::leanh::LeanObject,
    mut v_k_4221_: *mut crate::leanh::LeanObject,
    mut v_nondep_4222_: u8,
    mut v_kind_4223_: u8,
    mut v___y_4224_: *mut crate::leanh::LeanObject,
    mut v___y_4225_: *mut crate::leanh::LeanObject,
    mut v___y_4226_: *mut crate::leanh::LeanObject,
    mut v___y_4227_: *mut crate::leanh::LeanObject,
    mut v___y_4228_: *mut crate::leanh::LeanObject,
    mut v___y_4229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4231_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15___redArg(v_name_4218_, v_type_4219_, v_val_4220_, v_k_4221_, v_nondep_4222_, v_kind_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_);
    return v___x_4231_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15___boxed(
    mut v_00_u03b1_4232_: *mut crate::leanh::LeanObject,
    mut v_name_4233_: *mut crate::leanh::LeanObject,
    mut v_type_4234_: *mut crate::leanh::LeanObject,
    mut v_val_4235_: *mut crate::leanh::LeanObject,
    mut v_k_4236_: *mut crate::leanh::LeanObject,
    mut v_nondep_4237_: *mut crate::leanh::LeanObject,
    mut v_kind_4238_: *mut crate::leanh::LeanObject,
    mut v___y_4239_: *mut crate::leanh::LeanObject,
    mut v___y_4240_: *mut crate::leanh::LeanObject,
    mut v___y_4241_: *mut crate::leanh::LeanObject,
    mut v___y_4242_: *mut crate::leanh::LeanObject,
    mut v___y_4243_: *mut crate::leanh::LeanObject,
    mut v___y_4244_: *mut crate::leanh::LeanObject,
    mut v___y_4245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nondep_boxed_4246_: u8 = 0;
    let mut v_kind_boxed_4247_: u8 = 0;
    let mut v_res_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_4246_ = (crate::leanh::lean_unbox(v_nondep_4237_) as u8);
    v_kind_boxed_4247_ = (crate::leanh::lean_unbox(v_kind_4238_) as u8);
    v_res_4248_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__5_spec__12_spec__15(v_00_u03b1_4232_, v_name_4233_, v_type_4234_, v_val_4235_, v_k_4236_, v_nondep_boxed_4246_, v_kind_boxed_4247_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_);
    crate::leanh::lean_dec(v___y_4244_);
    crate::leanh::lean_dec_ref(v___y_4243_);
    crate::leanh::lean_dec(v___y_4242_);
    crate::leanh::lean_dec_ref(v___y_4241_);
    crate::leanh::lean_dec(v___y_4240_);
    crate::leanh::lean_dec(v___y_4239_);
    return v_res_4248_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6(
    mut v_00_u03b2_4249_: *mut crate::leanh::LeanObject,
    mut v_i_4250_: *mut crate::leanh::LeanObject,
    mut v_source_4251_: *mut crate::leanh::LeanObject,
    mut v_target_4252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4253_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v_i_4250_, v_source_4251_, v_target_4252_);
    return v___x_4253_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6_spec__10(
    mut v_00_u03b2_4254_: *mut crate::leanh::LeanObject,
    mut v_x_4255_: *mut crate::leanh::LeanObject,
    mut v_x_4256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4257_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs_spec__0_spec__0_spec__2_spec__5_spec__6_spec__10___redArg(v_x_4255_, v_x_4256_);
    return v___x_4257_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg___lam__0(
    mut v_k_4258_: *mut crate::leanh::LeanObject,
    mut v___y_4259_: *mut crate::leanh::LeanObject,
    mut v_b_4260_: *mut crate::leanh::LeanObject,
    mut v_c_4261_: *mut crate::leanh::LeanObject,
    mut v___y_4262_: *mut crate::leanh::LeanObject,
    mut v___y_4263_: *mut crate::leanh::LeanObject,
    mut v___y_4264_: *mut crate::leanh::LeanObject,
    mut v___y_4265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_4265_);
    crate::leanh::lean_inc_ref(v___y_4264_);
    crate::leanh::lean_inc(v___y_4263_);
    crate::leanh::lean_inc_ref(v___y_4262_);
    crate::leanh::lean_inc(v___y_4259_);
    v___x_4267_ = crate::leanh::lean_apply_8(
        v_k_4258_,
        v_b_4260_,
        v_c_4261_,
        v___y_4259_,
        v___y_4262_,
        v___y_4263_,
        v___y_4264_,
        v___y_4265_,
        crate::leanh::lean_box(0),
    );
    return v___x_4267_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg___lam__0___boxed(
    mut v_k_4268_: *mut crate::leanh::LeanObject,
    mut v___y_4269_: *mut crate::leanh::LeanObject,
    mut v_b_4270_: *mut crate::leanh::LeanObject,
    mut v_c_4271_: *mut crate::leanh::LeanObject,
    mut v___y_4272_: *mut crate::leanh::LeanObject,
    mut v___y_4273_: *mut crate::leanh::LeanObject,
    mut v___y_4274_: *mut crate::leanh::LeanObject,
    mut v___y_4275_: *mut crate::leanh::LeanObject,
    mut v___y_4276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4277_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg___lam__0(v_k_4268_, v___y_4269_, v_b_4270_, v_c_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_);
    crate::leanh::lean_dec(v___y_4275_);
    crate::leanh::lean_dec_ref(v___y_4274_);
    crate::leanh::lean_dec(v___y_4273_);
    crate::leanh::lean_dec_ref(v___y_4272_);
    crate::leanh::lean_dec(v___y_4269_);
    return v_res_4277_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg(
    mut v_type_4278_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_4279_: *mut crate::leanh::LeanObject,
    mut v_k_4280_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4281_: u8,
    mut v_whnfType_4282_: u8,
    mut v___y_4283_: *mut crate::leanh::LeanObject,
    mut v___y_4284_: *mut crate::leanh::LeanObject,
    mut v___y_4285_: *mut crate::leanh::LeanObject,
    mut v___y_4286_: *mut crate::leanh::LeanObject,
    mut v___y_4287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4294_: u8 = 0;
    let mut v___x_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4298_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_4283_);
                v___f_4289_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 2);
                crate::leanh::lean_closure_set(v___f_4289_, 0, v_k_4280_);
                crate::leanh::lean_closure_set(v___f_4289_, 1, v___y_4283_);
                v___x_4290_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    crate::leanh::lean_box(0),
                    v_type_4278_,
                    v_maxFVars_x3f_4279_,
                    v___f_4289_,
                    v_cleanupAnnotations_4281_,
                    v_whnfType_4282_,
                    v___y_4284_,
                    v___y_4285_,
                    v___y_4286_,
                    v___y_4287_,
                );
                if crate::leanh::lean_obj_tag(v___x_4290_) == 0 {
                    return v___x_4290_;
                } else {
                    v_a_4291_ = crate::leanh::lean_ctor_get(v___x_4290_, 0);
                    v_isSharedCheck_4298_ = (!crate::leanh::lean_is_exclusive(v___x_4290_)) as u8;
                    if v_isSharedCheck_4298_ == 0 {
                        v___x_4293_ = v___x_4290_;
                        v_isShared_4294_ = v_isSharedCheck_4298_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4291_);
                        crate::leanh::lean_dec(v___x_4290_);
                        v___x_4293_ = crate::leanh::lean_box(0);
                        v_isShared_4294_ = v_isSharedCheck_4298_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4294_ == 0 {
                    v___x_4296_ = v___x_4293_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4297_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4297_, 0, v_a_4291_);
                    v___x_4296_ = v_reuseFailAlloc_4297_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4296_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg___boxed(
    mut v_type_4299_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_4300_: *mut crate::leanh::LeanObject,
    mut v_k_4301_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4302_: *mut crate::leanh::LeanObject,
    mut v_whnfType_4303_: *mut crate::leanh::LeanObject,
    mut v___y_4304_: *mut crate::leanh::LeanObject,
    mut v___y_4305_: *mut crate::leanh::LeanObject,
    mut v___y_4306_: *mut crate::leanh::LeanObject,
    mut v___y_4307_: *mut crate::leanh::LeanObject,
    mut v___y_4308_: *mut crate::leanh::LeanObject,
    mut v___y_4309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4310_: u8 = 0;
    let mut v_whnfType_boxed_4311_: u8 = 0;
    let mut v_res_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4310_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_4302_) as u8);
    v_whnfType_boxed_4311_ = (crate::leanh::lean_unbox(v_whnfType_4303_) as u8);
    v_res_4312_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg(v_type_4299_, v_maxFVars_x3f_4300_, v_k_4301_, v_cleanupAnnotations_boxed_4310_, v_whnfType_boxed_4311_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_);
    crate::leanh::lean_dec(v___y_4308_);
    crate::leanh::lean_dec_ref(v___y_4307_);
    crate::leanh::lean_dec(v___y_4306_);
    crate::leanh::lean_dec_ref(v___y_4305_);
    crate::leanh::lean_dec(v___y_4304_);
    return v_res_4312_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0(
    mut v_00_u03b1_4313_: *mut crate::leanh::LeanObject,
    mut v_type_4314_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_4315_: *mut crate::leanh::LeanObject,
    mut v_k_4316_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4317_: u8,
    mut v_whnfType_4318_: u8,
    mut v___y_4319_: *mut crate::leanh::LeanObject,
    mut v___y_4320_: *mut crate::leanh::LeanObject,
    mut v___y_4321_: *mut crate::leanh::LeanObject,
    mut v___y_4322_: *mut crate::leanh::LeanObject,
    mut v___y_4323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4325_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg(v_type_4314_, v_maxFVars_x3f_4315_, v_k_4316_, v_cleanupAnnotations_4317_, v_whnfType_4318_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_);
    return v___x_4325_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___boxed(
    mut v_00_u03b1_4326_: *mut crate::leanh::LeanObject,
    mut v_type_4327_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_4328_: *mut crate::leanh::LeanObject,
    mut v_k_4329_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4330_: *mut crate::leanh::LeanObject,
    mut v_whnfType_4331_: *mut crate::leanh::LeanObject,
    mut v___y_4332_: *mut crate::leanh::LeanObject,
    mut v___y_4333_: *mut crate::leanh::LeanObject,
    mut v___y_4334_: *mut crate::leanh::LeanObject,
    mut v___y_4335_: *mut crate::leanh::LeanObject,
    mut v___y_4336_: *mut crate::leanh::LeanObject,
    mut v___y_4337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4338_: u8 = 0;
    let mut v_whnfType_boxed_4339_: u8 = 0;
    let mut v_res_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4338_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_4330_) as u8);
    v_whnfType_boxed_4339_ = (crate::leanh::lean_unbox(v_whnfType_4331_) as u8);
    v_res_4340_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0(v_00_u03b1_4326_, v_type_4327_, v_maxFVars_x3f_4328_, v_k_4329_, v_cleanupAnnotations_boxed_4338_, v_whnfType_boxed_4339_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_);
    crate::leanh::lean_dec(v___y_4336_);
    crate::leanh::lean_dec_ref(v___y_4335_);
    crate::leanh::lean_dec(v___y_4334_);
    crate::leanh::lean_dec_ref(v___y_4333_);
    crate::leanh::lean_dec(v___y_4332_);
    return v_res_4340_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___lam__0___boxed(
    mut v_currentBinderIdx_4341_: *mut crate::leanh::LeanObject,
    mut v___x_4342_: *mut crate::leanh::LeanObject,
    mut v_currentFVars_4343_: *mut crate::leanh::LeanObject,
    mut v_p_4344_: *mut crate::leanh::LeanObject,
    mut v_fvar_4345_: *mut crate::leanh::LeanObject,
    mut v_e_4346_: *mut crate::leanh::LeanObject,
    mut v___y_4347_: *mut crate::leanh::LeanObject,
    mut v___y_4348_: *mut crate::leanh::LeanObject,
    mut v___y_4349_: *mut crate::leanh::LeanObject,
    mut v___y_4350_: *mut crate::leanh::LeanObject,
    mut v___y_4351_: *mut crate::leanh::LeanObject,
    mut v___y_4352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4353_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___lam__0(v_currentBinderIdx_4341_, v___x_4342_, v_currentFVars_4343_, v_p_4344_, v_fvar_4345_, v_e_4346_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_);
    crate::leanh::lean_dec(v___y_4351_);
    crate::leanh::lean_dec_ref(v___y_4350_);
    crate::leanh::lean_dec(v___y_4349_);
    crate::leanh::lean_dec_ref(v___y_4348_);
    crate::leanh::lean_dec(v___y_4347_);
    crate::leanh::lean_dec_ref(v_fvar_4345_);
    crate::leanh::lean_dec(v___x_4342_);
    return v_res_4353_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go(
    mut v_p_4356_: *mut crate::leanh::LeanObject,
    mut v_e_4357_: *mut crate::leanh::LeanObject,
    mut v_currentBinderIdx_4358_: *mut crate::leanh::LeanObject,
    mut v_currentFVars_4359_: *mut crate::leanh::LeanObject,
    mut v_a_4360_: *mut crate::leanh::LeanObject,
    mut v_a_4361_: *mut crate::leanh::LeanObject,
    mut v_a_4362_: *mut crate::leanh::LeanObject,
    mut v_a_4363_: *mut crate::leanh::LeanObject,
    mut v_a_4364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_e_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: u8 = 0;
    let mut v_type_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4378_: u8 = 0;
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4382_: u8 = 0;
    let mut v_a_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4386_: u8 = 0;
    let mut v___x_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4390_: u8 = 0;
    let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4394_: u8 = 0;
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4398_: u8 = 0;
    let mut v_unused_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4403_: u8 = 0;
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4407_: u8 = 0;
    let mut v_binderType_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4411_: u8 = 0;
    let mut v___x_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4422_: u8 = 0;
    let mut v___x_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4426_: u8 = 0;
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: u8 = 0;
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: u8 = 0;
    let mut v___x_4433_: u8 = 0;
    let mut v___x_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: u8 = 0;
    let mut v_a_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4439_: u8 = 0;
    let mut v___x_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4443_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_e_4366_ = l_Lean_Expr_cleanupAnnotations(v_e_4357_);
                v___x_4367_ = l_Lean_Expr_isForall(v_e_4366_);
                if v___x_4367_ == 0 {
                    if crate::leanh::lean_obj_tag(v_e_4366_) == 8 {
                        v_type_4368_ = crate::leanh::lean_ctor_get(v_e_4366_, 1);
                        crate::leanh::lean_inc_ref_n(v_type_4368_, 2);
                        v_body_4369_ = crate::leanh::lean_ctor_get(v_e_4366_, 3);
                        crate::leanh::lean_inc_ref(v_body_4369_);
                        crate::leanh::lean_dec_ref_known(v_e_4366_, 4);
                        v___x_4370_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs(v_type_4368_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_);
                        if crate::leanh::lean_obj_tag(v___x_4370_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4370_, 1);
                            v___x_4371_ = l_Lean_Meta_mkSorry(
                                v_type_4368_,
                                v___x_4367_,
                                v_a_4361_,
                                v_a_4362_,
                                v_a_4363_,
                                v_a_4364_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4371_) == 0 {
                                v_a_4372_ = crate::leanh::lean_ctor_get(v___x_4371_, 0);
                                crate::leanh::lean_inc(v_a_4372_);
                                crate::leanh::lean_dec_ref_known(v___x_4371_, 1);
                                v___x_4373_ = lean_expr_instantiate1(v_body_4369_, v_a_4372_);
                                crate::leanh::lean_dec(v_a_4372_);
                                crate::leanh::lean_dec_ref(v_body_4369_);
                                v_e_4357_ = v___x_4373_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_body_4369_);
                                crate::leanh::lean_dec_ref(v_currentFVars_4359_);
                                crate::leanh::lean_dec(v_currentBinderIdx_4358_);
                                crate::leanh::lean_dec_ref(v_p_4356_);
                                v_a_4375_ = crate::leanh::lean_ctor_get(v___x_4371_, 0);
                                v_isSharedCheck_4382_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4371_)) as u8;
                                if v_isSharedCheck_4382_ == 0 {
                                    v___x_4377_ = v___x_4371_;
                                    v_isShared_4378_ = v_isSharedCheck_4382_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4375_);
                                    crate::leanh::lean_dec(v___x_4371_);
                                    v___x_4377_ = crate::leanh::lean_box(0);
                                    v_isShared_4378_ = v_isSharedCheck_4382_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_body_4369_);
                            crate::leanh::lean_dec_ref(v_type_4368_);
                            crate::leanh::lean_dec_ref(v_currentFVars_4359_);
                            crate::leanh::lean_dec(v_currentBinderIdx_4358_);
                            crate::leanh::lean_dec_ref(v_p_4356_);
                            v_a_4383_ = crate::leanh::lean_ctor_get(v___x_4370_, 0);
                            v_isSharedCheck_4390_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4370_)) as u8;
                            if v_isSharedCheck_4390_ == 0 {
                                v___x_4385_ = v___x_4370_;
                                v_isShared_4386_ = v_isSharedCheck_4390_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4383_);
                                crate::leanh::lean_dec(v___x_4370_);
                                v___x_4385_ = crate::leanh::lean_box(0);
                                v_isShared_4386_ = v_isSharedCheck_4390_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_currentBinderIdx_4358_);
                        crate::leanh::lean_dec_ref(v_p_4356_);
                        v___x_4391_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs(v_e_4366_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_);
                        if crate::leanh::lean_obj_tag(v___x_4391_) == 0 {
                            v_isSharedCheck_4398_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4391_)) as u8;
                            if v_isSharedCheck_4398_ == 0 {
                                v_unused_4399_ = crate::leanh::lean_ctor_get(v___x_4391_, 0);
                                crate::leanh::lean_dec(v_unused_4399_);
                                v___x_4393_ = v___x_4391_;
                                v_isShared_4394_ = v_isSharedCheck_4398_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_4391_);
                                v___x_4393_ = crate::leanh::lean_box(0);
                                v_isShared_4394_ = v_isSharedCheck_4398_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_currentFVars_4359_);
                            v_a_4400_ = crate::leanh::lean_ctor_get(v___x_4391_, 0);
                            v_isSharedCheck_4407_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4391_)) as u8;
                            if v_isSharedCheck_4407_ == 0 {
                                v___x_4402_ = v___x_4391_;
                                v_isShared_4403_ = v_isSharedCheck_4407_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4400_);
                                crate::leanh::lean_dec(v___x_4391_);
                                v___x_4402_ = crate::leanh::lean_box(0);
                                v_isShared_4403_ = v_isSharedCheck_4407_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    v_binderType_4408_ = crate::leanh::lean_ctor_get(v_e_4366_, 1);
                    crate::leanh::lean_inc_ref_n(v_binderType_4408_, 2);
                    v___x_4409_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectFVarsOutsideOfProofs(v_binderType_4408_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_);
                    if crate::leanh::lean_obj_tag(v___x_4409_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4409_, 1);
                        v___x_4432_ = l_Lean_Expr_binderInfo(v_e_4366_);
                        v___x_4433_ = l_Lean_BinderInfo_isInstImplicit(v___x_4432_);
                        if v___x_4433_ == 0 {
                            v___y_4411_ = v___x_4433_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc_ref(v_p_4356_);
                            crate::leanh::lean_inc_ref(v_binderType_4408_);
                            v___x_4434_ = crate::leanh::lean_apply_1(v_p_4356_, v_binderType_4408_);
                            v___x_4435_ = (crate::leanh::lean_unbox(v___x_4434_) as u8);
                            v___y_4411_ = v___x_4435_;
                            state = 9;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_binderType_4408_);
                        crate::leanh::lean_dec_ref(v_e_4366_);
                        crate::leanh::lean_dec_ref(v_currentFVars_4359_);
                        crate::leanh::lean_dec(v_currentBinderIdx_4358_);
                        crate::leanh::lean_dec_ref(v_p_4356_);
                        v_a_4436_ = crate::leanh::lean_ctor_get(v___x_4409_, 0);
                        v_isSharedCheck_4443_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4409_)) as u8;
                        if v_isSharedCheck_4443_ == 0 {
                            v___x_4438_ = v___x_4409_;
                            v_isShared_4439_ = v_isSharedCheck_4443_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4436_);
                            crate::leanh::lean_dec(v___x_4409_);
                            v___x_4438_ = crate::leanh::lean_box(0);
                            v_isShared_4439_ = v_isSharedCheck_4443_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4378_ == 0 {
                    v___x_4380_ = v___x_4377_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4381_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4381_, 0, v_a_4375_);
                    v___x_4380_ = v_reuseFailAlloc_4381_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4380_;
            }
            3 => {
                if v_isShared_4386_ == 0 {
                    v___x_4388_ = v___x_4385_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4389_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4389_, 0, v_a_4383_);
                    v___x_4388_ = v_reuseFailAlloc_4389_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4388_;
            }
            5 => {
                if v_isShared_4394_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4393_, 0, v_currentFVars_4359_);
                    v___x_4396_ = v___x_4393_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4397_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4397_, 0, v_currentFVars_4359_);
                    v___x_4396_ = v_reuseFailAlloc_4397_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4396_;
            }
            7 => {
                if v_isShared_4403_ == 0 {
                    v___x_4405_ = v___x_4402_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4406_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4406_, 0, v_a_4400_);
                    v___x_4405_ = v_reuseFailAlloc_4406_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4405_;
            }
            9 => {
                if v___y_4411_ == 0 {
                    v___x_4412_ = l_Lean_Meta_mkSorry(
                        v_binderType_4408_,
                        v___y_4411_,
                        v_a_4361_,
                        v_a_4362_,
                        v_a_4363_,
                        v_a_4364_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4412_) == 0 {
                        v_a_4413_ = crate::leanh::lean_ctor_get(v___x_4412_, 0);
                        crate::leanh::lean_inc(v_a_4413_);
                        crate::leanh::lean_dec_ref_known(v___x_4412_, 1);
                        v_body_4414_ = crate::leanh::lean_ctor_get(v_e_4366_, 2);
                        crate::leanh::lean_inc_ref(v_body_4414_);
                        crate::leanh::lean_dec_ref(v_e_4366_);
                        v___x_4415_ = lean_expr_instantiate1(v_body_4414_, v_a_4413_);
                        crate::leanh::lean_dec(v_a_4413_);
                        crate::leanh::lean_dec_ref(v_body_4414_);
                        v___x_4416_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4417_ = lean_nat_add(v_currentBinderIdx_4358_, v___x_4416_);
                        crate::leanh::lean_dec(v_currentBinderIdx_4358_);
                        v_e_4357_ = v___x_4415_;
                        v_currentBinderIdx_4358_ = v___x_4417_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_e_4366_);
                        crate::leanh::lean_dec_ref(v_currentFVars_4359_);
                        crate::leanh::lean_dec(v_currentBinderIdx_4358_);
                        crate::leanh::lean_dec_ref(v_p_4356_);
                        v_a_4419_ = crate::leanh::lean_ctor_get(v___x_4412_, 0);
                        v_isSharedCheck_4426_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4412_)) as u8;
                        if v_isSharedCheck_4426_ == 0 {
                            v___x_4421_ = v___x_4412_;
                            v_isShared_4422_ = v_isSharedCheck_4426_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4419_);
                            crate::leanh::lean_dec(v___x_4412_);
                            v___x_4421_ = crate::leanh::lean_box(0);
                            v_isShared_4422_ = v_isSharedCheck_4426_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_binderType_4408_);
                    v___x_4427_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___f_4428_ = crate::leanh::lean_alloc_closure(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___lam__0___boxed as *mut core::ffi::c_void, 12, 4);
                    crate::leanh::lean_closure_set(v___f_4428_, 0, v_currentBinderIdx_4358_);
                    crate::leanh::lean_closure_set(v___f_4428_, 1, v___x_4427_);
                    crate::leanh::lean_closure_set(v___f_4428_, 2, v_currentFVars_4359_);
                    crate::leanh::lean_closure_set(v___f_4428_, 3, v_p_4356_);
                    v___x_4429_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___closed__0;
                    v___x_4430_ = 0;
                    v___x_4431_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go_spec__0___redArg(v_e_4366_, v___x_4429_, v___f_4428_, v___x_4430_, v___x_4430_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_);
                    return v___x_4431_;
                }
            }
            10 => {
                if v_isShared_4422_ == 0 {
                    v___x_4424_ = v___x_4421_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4425_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_a_4419_);
                    v___x_4424_ = v_reuseFailAlloc_4425_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4424_;
            }
            12 => {
                if v_isShared_4439_ == 0 {
                    v___x_4441_ = v___x_4438_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4442_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4442_, 0, v_a_4436_);
                    v___x_4441_ = v_reuseFailAlloc_4442_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4441_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___lam__0(
    mut v_currentBinderIdx_4444_: *mut crate::leanh::LeanObject,
    mut v___x_4445_: *mut crate::leanh::LeanObject,
    mut v_currentFVars_4446_: *mut crate::leanh::LeanObject,
    mut v_p_4447_: *mut crate::leanh::LeanObject,
    mut v_fvar_4448_: *mut crate::leanh::LeanObject,
    mut v_e_4449_: *mut crate::leanh::LeanObject,
    mut v___y_4450_: *mut crate::leanh::LeanObject,
    mut v___y_4451_: *mut crate::leanh::LeanObject,
    mut v___y_4452_: *mut crate::leanh::LeanObject,
    mut v___y_4453_: *mut crate::leanh::LeanObject,
    mut v___y_4454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4456_ = l_Lean_instInhabitedExpr;
    v___x_4457_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4458_ = lean_array_get_borrowed(v___x_4456_, v_fvar_4448_, v___x_4457_);
    v___x_4459_ = l_Lean_Expr_fvarId_x21(v___x_4458_);
    v___x_4460_ = lean_nat_add(v_currentBinderIdx_4444_, v___x_4445_);
    v___x_4461_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4461_, 0, v___x_4459_);
    crate::leanh::lean_ctor_set(v___x_4461_, 1, v_currentBinderIdx_4444_);
    v___x_4462_ = lean_array_push(v_currentFVars_4446_, v___x_4461_);
    v___x_4463_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go(v_p_4447_, v_e_4449_, v___x_4460_, v___x_4462_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
    return v___x_4463_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go___boxed(
    mut v_p_4464_: *mut crate::leanh::LeanObject,
    mut v_e_4465_: *mut crate::leanh::LeanObject,
    mut v_currentBinderIdx_4466_: *mut crate::leanh::LeanObject,
    mut v_currentFVars_4467_: *mut crate::leanh::LeanObject,
    mut v_a_4468_: *mut crate::leanh::LeanObject,
    mut v_a_4469_: *mut crate::leanh::LeanObject,
    mut v_a_4470_: *mut crate::leanh::LeanObject,
    mut v_a_4471_: *mut crate::leanh::LeanObject,
    mut v_a_4472_: *mut crate::leanh::LeanObject,
    mut v_a_4473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4474_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go(v_p_4464_, v_e_4465_, v_currentBinderIdx_4466_, v_currentFVars_4467_, v_a_4468_, v_a_4469_, v_a_4470_, v_a_4471_, v_a_4472_);
    crate::leanh::lean_dec(v_a_4472_);
    crate::leanh::lean_dec_ref(v_a_4471_);
    crate::leanh::lean_dec(v_a_4470_);
    crate::leanh::lean_dec_ref(v_a_4469_);
    crate::leanh::lean_dec(v_a_4468_);
    return v_res_4474_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0___redArg(
    mut v_k_4475_: *mut crate::leanh::LeanObject,
    mut v_t_4476_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: u8 = 0;
    let mut v___x_4482_: u8 = 0;
    let mut v___x_4484_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_4476_) == 0 {
                    v_k_4477_ = crate::leanh::lean_ctor_get(v_t_4476_, 1);
                    v_l_4478_ = crate::leanh::lean_ctor_get(v_t_4476_, 3);
                    v_r_4479_ = crate::leanh::lean_ctor_get(v_t_4476_, 4);
                    v___x_4480_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4475_, v_k_4477_);
                    match v___x_4480_ {
                        0 => {
                            v_t_4476_ = v_l_4478_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v___x_4482_ = 1;
                            return v___x_4482_;
                        }
                        _ => {
                            v_t_4476_ = v_r_4479_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_4484_ = 0;
                    return v___x_4484_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0___redArg___boxed(
    mut v_k_4485_: *mut crate::leanh::LeanObject,
    mut v_t_4486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4487_: u8 = 0;
    let mut v_r_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4487_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0___redArg(v_k_4485_, v_t_4486_);
    crate::leanh::lean_dec(v_t_4486_);
    crate::leanh::lean_dec(v_k_4485_);
    v_r_4488_ = crate::leanh::lean_box((v_res_4487_) as usize);
    return v_r_4488_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1_spec__1(
    mut v_val_4489_: *mut crate::leanh::LeanObject,
    mut v_as_4490_: *mut crate::leanh::LeanObject,
    mut v_i_4491_: usize,
    mut v_stop_4492_: usize,
    mut v_b_4493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: usize = 0;
    let mut v___x_4497_: usize = 0;
    let mut v___x_4499_: u8 = 0;
    let mut v___x_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: u8 = 0;
    let mut v___x_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4499_ = lean_usize_dec_eq(v_i_4491_, v_stop_4492_);
                if v___x_4499_ == 0 {
                    v___x_4500_ = lean_array_uget_borrowed(v_as_4490_, v_i_4491_);
                    v_fvarId_4501_ = crate::leanh::lean_ctor_get(v___x_4500_, 0);
                    v_idx_4502_ = crate::leanh::lean_ctor_get(v___x_4500_, 1);
                    v___x_4503_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0___redArg(v_fvarId_4501_, v_val_4489_);
                    if v___x_4503_ == 0 {
                        crate::leanh::lean_inc(v_idx_4502_);
                        v___x_4504_ = lean_array_push(v_b_4493_, v_idx_4502_);
                        v___y_4495_ = v___x_4504_;
                        state = 1;
                        continue;
                    } else {
                        v___y_4495_ = v_b_4493_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_4493_;
                }
            }
            1 => {
                v___x_4496_ = 1usize;
                v___x_4497_ = lean_usize_add(v_i_4491_, v___x_4496_);
                v_i_4491_ = v___x_4497_;
                v_b_4493_ = v___y_4495_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1_spec__1___boxed(
    mut v_val_4505_: *mut crate::leanh::LeanObject,
    mut v_as_4506_: *mut crate::leanh::LeanObject,
    mut v_i_4507_: *mut crate::leanh::LeanObject,
    mut v_stop_4508_: *mut crate::leanh::LeanObject,
    mut v_b_4509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4510_: usize = 0;
    let mut v_stop_boxed_4511_: usize = 0;
    let mut v_res_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4510_ = crate::leanh::lean_unbox_usize(v_i_4507_);
    crate::leanh::lean_dec(v_i_4507_);
    v_stop_boxed_4511_ = crate::leanh::lean_unbox_usize(v_stop_4508_);
    crate::leanh::lean_dec(v_stop_4508_);
    v_res_4512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1_spec__1(v_val_4505_, v_as_4506_, v_i_boxed_4510_, v_stop_boxed_4511_, v_b_4509_);
    crate::leanh::lean_dec_ref(v_as_4506_);
    crate::leanh::lean_dec(v_val_4505_);
    return v_res_4512_;
}
pub unsafe fn l_Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1(
    mut v_val_4513_: *mut crate::leanh::LeanObject,
    mut v_as_4514_: *mut crate::leanh::LeanObject,
    mut v_start_4515_: *mut crate::leanh::LeanObject,
    mut v_stop_4516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: u8 = 0;
    v___x_4517_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere___closed__0;
    v___x_4518_ = lean_nat_dec_lt(v_start_4515_, v_stop_4516_);
    if v___x_4518_ == 0 {
        return v___x_4517_;
    } else {
        let mut v___x_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4520_: u8 = 0;
        v___x_4519_ = lean_array_get_size(v_as_4514_);
        v___x_4520_ = lean_nat_dec_le(v_stop_4516_, v___x_4519_);
        if v___x_4520_ == 0 {
            let mut v___x_4521_: u8 = 0;
            v___x_4521_ = lean_nat_dec_lt(v_start_4515_, v___x_4519_);
            if v___x_4521_ == 0 {
                return v___x_4517_;
            } else {
                let mut v___x_4522_: usize = 0;
                let mut v___x_4523_: usize = 0;
                let mut v___x_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4522_ = lean_usize_of_nat(v_start_4515_);
                v___x_4523_ = lean_usize_of_nat(v___x_4519_);
                v___x_4524_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1_spec__1(v_val_4513_, v_as_4514_, v___x_4522_, v___x_4523_, v___x_4517_);
                return v___x_4524_;
            }
        } else {
            let mut v___x_4525_: usize = 0;
            let mut v___x_4526_: usize = 0;
            let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4525_ = lean_usize_of_nat(v_start_4515_);
            v___x_4526_ = lean_usize_of_nat(v_stop_4516_);
            v___x_4527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1_spec__1(v_val_4513_, v_as_4514_, v___x_4525_, v___x_4526_, v___x_4517_);
            return v___x_4527_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1___boxed(
    mut v_val_4528_: *mut crate::leanh::LeanObject,
    mut v_as_4529_: *mut crate::leanh::LeanObject,
    mut v_start_4530_: *mut crate::leanh::LeanObject,
    mut v_stop_4531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4532_ = l_Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1(v_val_4528_, v_as_4529_, v_start_4530_, v_stop_4531_);
    crate::leanh::lean_dec(v_stop_4531_);
    crate::leanh::lean_dec(v_start_4530_);
    crate::leanh::lean_dec_ref(v_as_4529_);
    crate::leanh::lean_dec(v_val_4528_);
    return v_res_4532_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere(
    mut v_p_4535_: *mut crate::leanh::LeanObject,
    mut v_e_4536_: *mut crate::leanh::LeanObject,
    mut v_a_4537_: *mut crate::leanh::LeanObject,
    mut v_a_4538_: *mut crate::leanh::LeanObject,
    mut v_a_4539_: *mut crate::leanh::LeanObject,
    mut v_a_4540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4550_: u8 = 0;
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4557_: u8 = 0;
    let mut v_a_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4561_: u8 = 0;
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4565_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4542_ = crate::leanh::lean_box(1);
                v___x_4543_ = lean_st_mk_ref(v___x_4542_);
                v___x_4544_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4545_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere___closed__0;
                v___x_4546_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_go(v_p_4535_, v_e_4536_, v___x_4544_, v___x_4545_, v___x_4543_, v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_);
                if crate::leanh::lean_obj_tag(v___x_4546_) == 0 {
                    v_a_4547_ = crate::leanh::lean_ctor_get(v___x_4546_, 0);
                    v_isSharedCheck_4557_ = (!crate::leanh::lean_is_exclusive(v___x_4546_)) as u8;
                    if v_isSharedCheck_4557_ == 0 {
                        v___x_4549_ = v___x_4546_;
                        v_isShared_4550_ = v_isSharedCheck_4557_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4547_);
                        crate::leanh::lean_dec(v___x_4546_);
                        v___x_4549_ = crate::leanh::lean_box(0);
                        v_isShared_4550_ = v_isSharedCheck_4557_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4543_);
                    v_a_4558_ = crate::leanh::lean_ctor_get(v___x_4546_, 0);
                    v_isSharedCheck_4565_ = (!crate::leanh::lean_is_exclusive(v___x_4546_)) as u8;
                    if v_isSharedCheck_4565_ == 0 {
                        v___x_4560_ = v___x_4546_;
                        v_isShared_4561_ = v_isSharedCheck_4565_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4558_);
                        crate::leanh::lean_dec(v___x_4546_);
                        v___x_4560_ = crate::leanh::lean_box(0);
                        v_isShared_4561_ = v_isSharedCheck_4565_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4551_ = lean_st_ref_get(v___x_4543_);
                crate::leanh::lean_dec(v___x_4543_);
                v___x_4552_ = lean_array_get_size(v_a_4547_);
                v___x_4553_ = l_Array_filterMapM___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__1(v___x_4551_, v_a_4547_, v___x_4544_, v___x_4552_);
                crate::leanh::lean_dec(v_a_4547_);
                crate::leanh::lean_dec(v___x_4551_);
                if v_isShared_4550_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4549_, 0, v___x_4553_);
                    v___x_4555_ = v___x_4549_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4556_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4556_, 0, v___x_4553_);
                    v___x_4555_ = v_reuseFailAlloc_4556_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4555_;
            }
            3 => {
                if v_isShared_4561_ == 0 {
                    v___x_4563_ = v___x_4560_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4564_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4564_, 0, v_a_4558_);
                    v___x_4563_ = v_reuseFailAlloc_4564_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4563_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere___boxed(
    mut v_p_4566_: *mut crate::leanh::LeanObject,
    mut v_e_4567_: *mut crate::leanh::LeanObject,
    mut v_a_4568_: *mut crate::leanh::LeanObject,
    mut v_a_4569_: *mut crate::leanh::LeanObject,
    mut v_a_4570_: *mut crate::leanh::LeanObject,
    mut v_a_4571_: *mut crate::leanh::LeanObject,
    mut v_a_4572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4573_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere(v_p_4566_, v_e_4567_, v_a_4568_, v_a_4569_, v_a_4570_, v_a_4571_);
    crate::leanh::lean_dec(v_a_4571_);
    crate::leanh::lean_dec_ref(v_a_4570_);
    crate::leanh::lean_dec(v_a_4569_);
    crate::leanh::lean_dec_ref(v_a_4568_);
    return v_res_4573_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0(
    mut v_00_u03b2_4574_: *mut crate::leanh::LeanObject,
    mut v_k_4575_: *mut crate::leanh::LeanObject,
    mut v_t_4576_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4577_: u8 = 0;
    v___x_4577_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0___redArg(v_k_4575_, v_t_4576_);
    return v___x_4577_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0___boxed(
    mut v_00_u03b2_4578_: *mut crate::leanh::LeanObject,
    mut v_k_4579_: *mut crate::leanh::LeanObject,
    mut v_t_4580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4581_: u8 = 0;
    let mut v_r_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4581_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere_spec__0(v_00_u03b2_4578_, v_k_4579_, v_t_4580_);
    crate::leanh::lean_dec(v_t_4580_);
    crate::leanh::lean_dec(v_k_4579_);
    v_r_4582_ = crate::leanh::lean_box((v_res_4581_) as usize);
    return v_r_4582_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg___lam__0(
    mut v_k_4583_: *mut crate::leanh::LeanObject,
    mut v___y_4584_: *mut crate::leanh::LeanObject,
    mut v___y_4585_: *mut crate::leanh::LeanObject,
    mut v_b_4586_: *mut crate::leanh::LeanObject,
    mut v_c_4587_: *mut crate::leanh::LeanObject,
    mut v___y_4588_: *mut crate::leanh::LeanObject,
    mut v___y_4589_: *mut crate::leanh::LeanObject,
    mut v___y_4590_: *mut crate::leanh::LeanObject,
    mut v___y_4591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_4591_);
    crate::leanh::lean_inc_ref(v___y_4590_);
    crate::leanh::lean_inc(v___y_4589_);
    crate::leanh::lean_inc_ref(v___y_4588_);
    crate::leanh::lean_inc(v___y_4585_);
    crate::leanh::lean_inc_ref(v___y_4584_);
    v___x_4593_ = crate::leanh::lean_apply_9(
        v_k_4583_,
        v_b_4586_,
        v_c_4587_,
        v___y_4584_,
        v___y_4585_,
        v___y_4588_,
        v___y_4589_,
        v___y_4590_,
        v___y_4591_,
        crate::leanh::lean_box(0),
    );
    return v___x_4593_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg___lam__0___boxed(
    mut v_k_4594_: *mut crate::leanh::LeanObject,
    mut v___y_4595_: *mut crate::leanh::LeanObject,
    mut v___y_4596_: *mut crate::leanh::LeanObject,
    mut v_b_4597_: *mut crate::leanh::LeanObject,
    mut v_c_4598_: *mut crate::leanh::LeanObject,
    mut v___y_4599_: *mut crate::leanh::LeanObject,
    mut v___y_4600_: *mut crate::leanh::LeanObject,
    mut v___y_4601_: *mut crate::leanh::LeanObject,
    mut v___y_4602_: *mut crate::leanh::LeanObject,
    mut v___y_4603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4604_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg___lam__0(v_k_4594_, v___y_4595_, v___y_4596_, v_b_4597_, v_c_4598_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_);
    crate::leanh::lean_dec(v___y_4602_);
    crate::leanh::lean_dec_ref(v___y_4601_);
    crate::leanh::lean_dec(v___y_4600_);
    crate::leanh::lean_dec_ref(v___y_4599_);
    crate::leanh::lean_dec(v___y_4596_);
    crate::leanh::lean_dec_ref(v___y_4595_);
    return v_res_4604_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg(
    mut v_type_4605_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_4606_: *mut crate::leanh::LeanObject,
    mut v_k_4607_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4608_: u8,
    mut v_whnfType_4609_: u8,
    mut v___y_4610_: *mut crate::leanh::LeanObject,
    mut v___y_4611_: *mut crate::leanh::LeanObject,
    mut v___y_4612_: *mut crate::leanh::LeanObject,
    mut v___y_4613_: *mut crate::leanh::LeanObject,
    mut v___y_4614_: *mut crate::leanh::LeanObject,
    mut v___y_4615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4622_: u8 = 0;
    let mut v___x_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4626_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_4611_);
                crate::leanh::lean_inc_ref(v___y_4610_);
                v___f_4617_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
                crate::leanh::lean_closure_set(v___f_4617_, 0, v_k_4607_);
                crate::leanh::lean_closure_set(v___f_4617_, 1, v___y_4610_);
                crate::leanh::lean_closure_set(v___f_4617_, 2, v___y_4611_);
                v___x_4618_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    crate::leanh::lean_box(0),
                    v_type_4605_,
                    v_maxFVars_x3f_4606_,
                    v___f_4617_,
                    v_cleanupAnnotations_4608_,
                    v_whnfType_4609_,
                    v___y_4612_,
                    v___y_4613_,
                    v___y_4614_,
                    v___y_4615_,
                );
                if crate::leanh::lean_obj_tag(v___x_4618_) == 0 {
                    return v___x_4618_;
                } else {
                    v_a_4619_ = crate::leanh::lean_ctor_get(v___x_4618_, 0);
                    v_isSharedCheck_4626_ = (!crate::leanh::lean_is_exclusive(v___x_4618_)) as u8;
                    if v_isSharedCheck_4626_ == 0 {
                        v___x_4621_ = v___x_4618_;
                        v_isShared_4622_ = v_isSharedCheck_4626_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4619_);
                        crate::leanh::lean_dec(v___x_4618_);
                        v___x_4621_ = crate::leanh::lean_box(0);
                        v_isShared_4622_ = v_isSharedCheck_4626_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4622_ == 0 {
                    v___x_4624_ = v___x_4621_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4625_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_a_4619_);
                    v___x_4624_ = v_reuseFailAlloc_4625_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4624_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg___boxed(
    mut v_type_4627_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_4628_: *mut crate::leanh::LeanObject,
    mut v_k_4629_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4630_: *mut crate::leanh::LeanObject,
    mut v_whnfType_4631_: *mut crate::leanh::LeanObject,
    mut v___y_4632_: *mut crate::leanh::LeanObject,
    mut v___y_4633_: *mut crate::leanh::LeanObject,
    mut v___y_4634_: *mut crate::leanh::LeanObject,
    mut v___y_4635_: *mut crate::leanh::LeanObject,
    mut v___y_4636_: *mut crate::leanh::LeanObject,
    mut v___y_4637_: *mut crate::leanh::LeanObject,
    mut v___y_4638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4639_: u8 = 0;
    let mut v_whnfType_boxed_4640_: u8 = 0;
    let mut v_res_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4639_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_4630_) as u8);
    v_whnfType_boxed_4640_ = (crate::leanh::lean_unbox(v_whnfType_4631_) as u8);
    v_res_4641_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg(v_type_4627_, v_maxFVars_x3f_4628_, v_k_4629_, v_cleanupAnnotations_boxed_4639_, v_whnfType_boxed_4640_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_);
    crate::leanh::lean_dec(v___y_4637_);
    crate::leanh::lean_dec_ref(v___y_4636_);
    crate::leanh::lean_dec(v___y_4635_);
    crate::leanh::lean_dec_ref(v___y_4634_);
    crate::leanh::lean_dec(v___y_4633_);
    crate::leanh::lean_dec_ref(v___y_4632_);
    return v_res_4641_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2(
    mut v_00_u03b1_4642_: *mut crate::leanh::LeanObject,
    mut v_type_4643_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_4644_: *mut crate::leanh::LeanObject,
    mut v_k_4645_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4646_: u8,
    mut v_whnfType_4647_: u8,
    mut v___y_4648_: *mut crate::leanh::LeanObject,
    mut v___y_4649_: *mut crate::leanh::LeanObject,
    mut v___y_4650_: *mut crate::leanh::LeanObject,
    mut v___y_4651_: *mut crate::leanh::LeanObject,
    mut v___y_4652_: *mut crate::leanh::LeanObject,
    mut v___y_4653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4655_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg(v_type_4643_, v_maxFVars_x3f_4644_, v_k_4645_, v_cleanupAnnotations_4646_, v_whnfType_4647_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_);
    return v___x_4655_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___boxed(
    mut v_00_u03b1_4656_: *mut crate::leanh::LeanObject,
    mut v_type_4657_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_4658_: *mut crate::leanh::LeanObject,
    mut v_k_4659_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4660_: *mut crate::leanh::LeanObject,
    mut v_whnfType_4661_: *mut crate::leanh::LeanObject,
    mut v___y_4662_: *mut crate::leanh::LeanObject,
    mut v___y_4663_: *mut crate::leanh::LeanObject,
    mut v___y_4664_: *mut crate::leanh::LeanObject,
    mut v___y_4665_: *mut crate::leanh::LeanObject,
    mut v___y_4666_: *mut crate::leanh::LeanObject,
    mut v___y_4667_: *mut crate::leanh::LeanObject,
    mut v___y_4668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4669_: u8 = 0;
    let mut v_whnfType_boxed_4670_: u8 = 0;
    let mut v_res_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4669_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_4660_) as u8);
    v_whnfType_boxed_4670_ = (crate::leanh::lean_unbox(v_whnfType_4661_) as u8);
    v_res_4671_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2(v_00_u03b1_4656_, v_type_4657_, v_maxFVars_x3f_4658_, v_k_4659_, v_cleanupAnnotations_boxed_4669_, v_whnfType_boxed_4670_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_, v___y_4667_);
    crate::leanh::lean_dec(v___y_4667_);
    crate::leanh::lean_dec_ref(v___y_4666_);
    crate::leanh::lean_dec(v___y_4665_);
    crate::leanh::lean_dec_ref(v___y_4664_);
    crate::leanh::lean_dec(v___y_4663_);
    crate::leanh::lean_dec_ref(v___y_4662_);
    return v_res_4671_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0_spec__0(
    mut v_a_4672_: *mut crate::leanh::LeanObject,
    mut v_as_4673_: *mut crate::leanh::LeanObject,
    mut v_i_4674_: usize,
    mut v_stop_4675_: usize,
) -> u8 {
    let mut v___x_4676_: u8 = 0;
    let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: u8 = 0;
    let mut v___x_4679_: usize = 0;
    let mut v___x_4680_: usize = 0;
    let mut v___x_4682_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4676_ = lean_usize_dec_eq(v_i_4674_, v_stop_4675_);
                if v___x_4676_ == 0 {
                    v___x_4677_ = lean_array_uget_borrowed(v_as_4673_, v_i_4674_);
                    v___x_4678_ = lean_nat_dec_eq(v_a_4672_, v___x_4677_);
                    if v___x_4678_ == 0 {
                        v___x_4679_ = 1usize;
                        v___x_4680_ = lean_usize_add(v_i_4674_, v___x_4679_);
                        v_i_4674_ = v___x_4680_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4678_;
                    }
                } else {
                    v___x_4682_ = 0;
                    return v___x_4682_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0_spec__0___boxed(
    mut v_a_4683_: *mut crate::leanh::LeanObject,
    mut v_as_4684_: *mut crate::leanh::LeanObject,
    mut v_i_4685_: *mut crate::leanh::LeanObject,
    mut v_stop_4686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4687_: usize = 0;
    let mut v_stop_boxed_4688_: usize = 0;
    let mut v_res_4689_: u8 = 0;
    let mut v_r_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4687_ = crate::leanh::lean_unbox_usize(v_i_4685_);
    crate::leanh::lean_dec(v_i_4685_);
    v_stop_boxed_4688_ = crate::leanh::lean_unbox_usize(v_stop_4686_);
    crate::leanh::lean_dec(v_stop_4686_);
    v_res_4689_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0_spec__0(v_a_4683_, v_as_4684_, v_i_boxed_4687_, v_stop_boxed_4688_);
    crate::leanh::lean_dec_ref(v_as_4684_);
    crate::leanh::lean_dec(v_a_4683_);
    v_r_4690_ = crate::leanh::lean_box((v_res_4689_) as usize);
    return v_r_4690_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0(
    mut v_as_4691_: *mut crate::leanh::LeanObject,
    mut v_a_4692_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: u8 = 0;
    v___x_4693_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4694_ = lean_array_get_size(v_as_4691_);
    v___x_4695_ = lean_nat_dec_lt(v___x_4693_, v___x_4694_);
    if v___x_4695_ == 0 {
        return v___x_4695_;
    } else {
        if v___x_4695_ == 0 {
            return v___x_4695_;
        } else {
            let mut v___x_4696_: usize = 0;
            let mut v___x_4697_: usize = 0;
            let mut v___x_4698_: u8 = 0;
            v___x_4696_ = 0usize;
            v___x_4697_ = lean_usize_of_nat(v___x_4694_);
            v___x_4698_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0_spec__0(v_a_4692_, v_as_4691_, v___x_4696_, v___x_4697_);
            return v___x_4698_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0___boxed(
    mut v_as_4699_: *mut crate::leanh::LeanObject,
    mut v_a_4700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4701_: u8 = 0;
    let mut v_r_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4701_ = l_Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0(v_as_4699_, v_a_4700_);
    crate::leanh::lean_dec(v_a_4700_);
    crate::leanh::lean_dec_ref(v_as_4699_);
    v_r_4702_ = crate::leanh::lean_box((v_res_4701_) as usize);
    return v_r_4702_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1___redArg(
    mut v___x_4703_: *mut crate::leanh::LeanObject,
    mut v___x_4704_: u8,
    mut v_fvars_4705_: *mut crate::leanh::LeanObject,
    mut v_sz_4706_: usize,
    mut v_i_4707_: usize,
    mut v_bs_4708_: *mut crate::leanh::LeanObject,
    mut v___y_4709_: *mut crate::leanh::LeanObject,
    mut v___y_4710_: *mut crate::leanh::LeanObject,
    mut v___y_4711_: *mut crate::leanh::LeanObject,
    mut v___y_4712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4714_: u8 = 0;
    let mut v___x_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4722_: u8 = 0;
    let mut v___x_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: usize = 0;
    let mut v___x_4725_: usize = 0;
    let mut v___x_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: u8 = 0;
    let mut v___x_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: u8 = 0;
    let mut v___x_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4743_: u8 = 0;
    let mut v___x_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4747_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4714_ = lean_usize_dec_lt(v_i_4707_, v_sz_4706_);
                if v___x_4714_ == 0 {
                    v___x_4715_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4715_, 0, v_bs_4708_);
                    return v___x_4715_;
                } else {
                    v_v_4716_ = lean_array_uget(v_bs_4708_, v_i_4707_);
                    v___x_4717_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4718_ = lean_array_uset(v_bs_4708_, v_i_4707_, v___x_4717_);
                    v___x_4732_ = lean_array_get_size(v_fvars_4705_);
                    v___x_4733_ = lean_nat_dec_lt(v_v_4716_, v___x_4732_);
                    if v___x_4733_ == 0 {
                        v___x_4734_ = crate::leanh::lean_box(0);
                        v___y_4729_ = v___x_4734_;
                        v_a_4730_ = v___x_4734_;
                        state = 2;
                        continue;
                    } else {
                        v___x_4735_ = lean_array_fget_borrowed(v_fvars_4705_, v_v_4716_);
                        crate::leanh::lean_inc_n(v___x_4735_, 2);
                        v___x_4736_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4736_, 0, v___x_4735_);
                        crate::leanh::lean_inc(v___y_4712_);
                        crate::leanh::lean_inc_ref(v___y_4711_);
                        crate::leanh::lean_inc(v___y_4710_);
                        crate::leanh::lean_inc_ref(v___y_4709_);
                        v___x_4737_ = lean_infer_type(
                            v___x_4735_,
                            v___y_4709_,
                            v___y_4710_,
                            v___y_4711_,
                            v___y_4712_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4737_) == 0 {
                            v_a_4738_ = crate::leanh::lean_ctor_get(v___x_4737_, 0);
                            crate::leanh::lean_inc(v_a_4738_);
                            crate::leanh::lean_dec_ref_known(v___x_4737_, 1);
                            v___x_4739_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4739_, 0, v_a_4738_);
                            v___y_4729_ = v___x_4736_;
                            v_a_4730_ = v___x_4739_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_4736_, 1);
                            crate::leanh::lean_dec_ref(v_bs_x27_4718_);
                            crate::leanh::lean_dec(v_v_4716_);
                            v_a_4740_ = crate::leanh::lean_ctor_get(v___x_4737_, 0);
                            v_isSharedCheck_4747_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4737_)) as u8;
                            if v_isSharedCheck_4747_ == 0 {
                                v___x_4742_ = v___x_4737_;
                                v_isShared_4743_ = v_isSharedCheck_4747_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4740_);
                                crate::leanh::lean_dec(v___x_4737_);
                                v___x_4742_ = crate::leanh::lean_box(0);
                                v_isShared_4743_ = v_isSharedCheck_4747_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4723_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4723_, 0, v___y_4720_);
                crate::leanh::lean_ctor_set(v___x_4723_, 1, v___y_4721_);
                crate::leanh::lean_ctor_set(v___x_4723_, 2, v_v_4716_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4723_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___y_4722_,
                );
                v___x_4724_ = 1usize;
                v___x_4725_ = lean_usize_add(v_i_4707_, v___x_4724_);
                v___x_4726_ = lean_array_uset(v_bs_x27_4718_, v_i_4707_, v___x_4723_);
                v_i_4707_ = v___x_4725_;
                v_bs_4708_ = v___x_4726_;
                state = 0;
                continue;
            }
            2 => {
                v___x_4731_ = l_Array_contains___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__0(v___x_4703_, v_v_4716_);
                if v___x_4731_ == 0 {
                    v___y_4720_ = v___y_4729_;
                    v___y_4721_ = v_a_4730_;
                    v___y_4722_ = v___x_4714_;
                    state = 1;
                    continue;
                } else {
                    v___y_4720_ = v___y_4729_;
                    v___y_4721_ = v_a_4730_;
                    v___y_4722_ = v___x_4704_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_4743_ == 0 {
                    v___x_4745_ = v___x_4742_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4746_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4746_, 0, v_a_4740_);
                    v___x_4745_ = v_reuseFailAlloc_4746_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4745_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1___redArg___boxed(
    mut v___x_4748_: *mut crate::leanh::LeanObject,
    mut v___x_4749_: *mut crate::leanh::LeanObject,
    mut v_fvars_4750_: *mut crate::leanh::LeanObject,
    mut v_sz_4751_: *mut crate::leanh::LeanObject,
    mut v_i_4752_: *mut crate::leanh::LeanObject,
    mut v_bs_4753_: *mut crate::leanh::LeanObject,
    mut v___y_4754_: *mut crate::leanh::LeanObject,
    mut v___y_4755_: *mut crate::leanh::LeanObject,
    mut v___y_4756_: *mut crate::leanh::LeanObject,
    mut v___y_4757_: *mut crate::leanh::LeanObject,
    mut v___y_4758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3507__boxed_4759_: u8 = 0;
    let mut v_sz_boxed_4760_: usize = 0;
    let mut v_i_boxed_4761_: usize = 0;
    let mut v_res_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3507__boxed_4759_ = (crate::leanh::lean_unbox(v___x_4749_) as u8);
    v_sz_boxed_4760_ = crate::leanh::lean_unbox_usize(v_sz_4751_);
    crate::leanh::lean_dec(v_sz_4751_);
    v_i_boxed_4761_ = crate::leanh::lean_unbox_usize(v_i_4752_);
    crate::leanh::lean_dec(v_i_4752_);
    v_res_4762_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1___redArg(v___x_4748_, v___x_3507__boxed_4759_, v_fvars_4750_, v_sz_boxed_4760_, v_i_boxed_4761_, v_bs_4753_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_);
    crate::leanh::lean_dec(v___y_4757_);
    crate::leanh::lean_dec_ref(v___y_4756_);
    crate::leanh::lean_dec(v___y_4755_);
    crate::leanh::lean_dec_ref(v___y_4754_);
    crate::leanh::lean_dec_ref(v_fvars_4750_);
    crate::leanh::lean_dec_ref(v___x_4748_);
    return v_res_4762_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere___lam__0(
    mut v_p_4763_: *mut crate::leanh::LeanObject,
    mut v_type_4764_: *mut crate::leanh::LeanObject,
    mut v_a_4765_: *mut crate::leanh::LeanObject,
    mut v___x_4766_: u8,
    mut v_logOnUnused_4767_: *mut crate::leanh::LeanObject,
    mut v_fvars_4768_: *mut crate::leanh::LeanObject,
    mut v_x_4769_: *mut crate::leanh::LeanObject,
    mut v___y_4770_: *mut crate::leanh::LeanObject,
    mut v___y_4771_: *mut crate::leanh::LeanObject,
    mut v___y_4772_: *mut crate::leanh::LeanObject,
    mut v___y_4773_: *mut crate::leanh::LeanObject,
    mut v___y_4774_: *mut crate::leanh::LeanObject,
    mut v___y_4775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4778_: usize = 0;
    let mut v___x_4779_: usize = 0;
    let mut v___x_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4786_: u8 = 0;
    let mut v___x_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4790_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4777_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_getUnusedForallInstanceBinderIdxsWhere(v_p_4763_, v_type_4764_);
                v_sz_4778_ = lean_array_size(v_a_4765_);
                v___x_4779_ = 0usize;
                v___x_4780_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1___redArg(v___x_4777_, v___x_4766_, v_fvars_4768_, v_sz_4778_, v___x_4779_, v_a_4765_, v___y_4772_, v___y_4773_, v___y_4774_, v___y_4775_);
                crate::leanh::lean_dec_ref(v___x_4777_);
                if crate::leanh::lean_obj_tag(v___x_4780_) == 0 {
                    v_a_4781_ = crate::leanh::lean_ctor_get(v___x_4780_, 0);
                    crate::leanh::lean_inc(v_a_4781_);
                    crate::leanh::lean_dec_ref_known(v___x_4780_, 1);
                    crate::leanh::lean_inc(v___y_4775_);
                    crate::leanh::lean_inc_ref(v___y_4774_);
                    crate::leanh::lean_inc(v___y_4773_);
                    crate::leanh::lean_inc_ref(v___y_4772_);
                    crate::leanh::lean_inc(v___y_4771_);
                    crate::leanh::lean_inc_ref(v___y_4770_);
                    v___x_4782_ = crate::leanh::lean_apply_8(
                        v_logOnUnused_4767_,
                        v_a_4781_,
                        v___y_4770_,
                        v___y_4771_,
                        v___y_4772_,
                        v___y_4773_,
                        v___y_4774_,
                        v___y_4775_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4782_;
                } else {
                    crate::leanh::lean_dec_ref(v_logOnUnused_4767_);
                    v_a_4783_ = crate::leanh::lean_ctor_get(v___x_4780_, 0);
                    v_isSharedCheck_4790_ = (!crate::leanh::lean_is_exclusive(v___x_4780_)) as u8;
                    if v_isSharedCheck_4790_ == 0 {
                        v___x_4785_ = v___x_4780_;
                        v_isShared_4786_ = v_isSharedCheck_4790_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4783_);
                        crate::leanh::lean_dec(v___x_4780_);
                        v___x_4785_ = crate::leanh::lean_box(0);
                        v_isShared_4786_ = v_isSharedCheck_4790_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4786_ == 0 {
                    v___x_4788_ = v___x_4785_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4789_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4789_, 0, v_a_4783_);
                    v___x_4788_ = v_reuseFailAlloc_4789_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4788_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere___lam__0___boxed(
    mut v_p_4791_: *mut crate::leanh::LeanObject,
    mut v_type_4792_: *mut crate::leanh::LeanObject,
    mut v_a_4793_: *mut crate::leanh::LeanObject,
    mut v___x_4794_: *mut crate::leanh::LeanObject,
    mut v_logOnUnused_4795_: *mut crate::leanh::LeanObject,
    mut v_fvars_4796_: *mut crate::leanh::LeanObject,
    mut v_x_4797_: *mut crate::leanh::LeanObject,
    mut v___y_4798_: *mut crate::leanh::LeanObject,
    mut v___y_4799_: *mut crate::leanh::LeanObject,
    mut v___y_4800_: *mut crate::leanh::LeanObject,
    mut v___y_4801_: *mut crate::leanh::LeanObject,
    mut v___y_4802_: *mut crate::leanh::LeanObject,
    mut v___y_4803_: *mut crate::leanh::LeanObject,
    mut v___y_4804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3592__boxed_4805_: u8 = 0;
    let mut v_res_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3592__boxed_4805_ = (crate::leanh::lean_unbox(v___x_4794_) as u8);
    v_res_4806_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere___lam__0(v_p_4791_, v_type_4792_, v_a_4793_, v___x_3592__boxed_4805_, v_logOnUnused_4795_, v_fvars_4796_, v_x_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_, v___y_4802_, v___y_4803_);
    crate::leanh::lean_dec(v___y_4803_);
    crate::leanh::lean_dec_ref(v___y_4802_);
    crate::leanh::lean_dec(v___y_4801_);
    crate::leanh::lean_dec_ref(v___y_4800_);
    crate::leanh::lean_dec(v___y_4799_);
    crate::leanh::lean_dec_ref(v___y_4798_);
    crate::leanh::lean_dec_ref(v_x_4797_);
    crate::leanh::lean_dec_ref(v_fvars_4796_);
    return v_res_4806_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere(
    mut v_decl_4807_: *mut crate::leanh::LeanObject,
    mut v_p_4808_: *mut crate::leanh::LeanObject,
    mut v_logOnUnused_4809_: *mut crate::leanh::LeanObject,
    mut v_a_4810_: *mut crate::leanh::LeanObject,
    mut v_a_4811_: *mut crate::leanh::LeanObject,
    mut v_a_4812_: *mut crate::leanh::LeanObject,
    mut v_a_4813_: *mut crate::leanh::LeanObject,
    mut v_a_4814_: *mut crate::leanh::LeanObject,
    mut v_a_4815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_type_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4822_: u8 = 0;
    let mut v___x_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: u8 = 0;
    let mut v___x_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: u8 = 0;
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4842_: u8 = 0;
    let mut v_a_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4846_: u8 = 0;
    let mut v___x_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4850_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_type_4817_ = crate::leanh::lean_ctor_get(v_decl_4807_, 2);
                crate::leanh::lean_inc_ref_n(v_type_4817_, 2);
                crate::leanh::lean_dec_ref(v_decl_4807_);
                crate::leanh::lean_inc_ref(v_p_4808_);
                v___x_4818_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_collectUnnecessaryInstanceBinderIdxsWhere(v_p_4808_, v_type_4817_, v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_);
                if crate::leanh::lean_obj_tag(v___x_4818_) == 0 {
                    v_a_4819_ = crate::leanh::lean_ctor_get(v___x_4818_, 0);
                    v_isSharedCheck_4842_ = (!crate::leanh::lean_is_exclusive(v___x_4818_)) as u8;
                    if v_isSharedCheck_4842_ == 0 {
                        v___x_4821_ = v___x_4818_;
                        v_isShared_4822_ = v_isSharedCheck_4842_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4819_);
                        crate::leanh::lean_dec(v___x_4818_);
                        v___x_4821_ = crate::leanh::lean_box(0);
                        v_isShared_4822_ = v_isSharedCheck_4842_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_4817_);
                    crate::leanh::lean_dec_ref(v_logOnUnused_4809_);
                    crate::leanh::lean_dec_ref(v_p_4808_);
                    v_a_4843_ = crate::leanh::lean_ctor_get(v___x_4818_, 0);
                    v_isSharedCheck_4850_ = (!crate::leanh::lean_is_exclusive(v___x_4818_)) as u8;
                    if v_isSharedCheck_4850_ == 0 {
                        v___x_4845_ = v___x_4818_;
                        v_isShared_4846_ = v_isSharedCheck_4850_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4843_);
                        crate::leanh::lean_dec(v___x_4818_);
                        v___x_4845_ = crate::leanh::lean_box(0);
                        v_isShared_4846_ = v_isSharedCheck_4850_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4823_ = lean_array_get_size(v_a_4819_);
                v___x_4824_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4825_ = lean_nat_sub(v___x_4823_, v___x_4824_);
                v___x_4826_ = lean_nat_dec_lt(v___x_4825_, v___x_4823_);
                if v___x_4826_ == 0 {
                    crate::leanh::lean_dec(v___x_4825_);
                    crate::leanh::lean_dec(v_a_4819_);
                    crate::leanh::lean_dec_ref(v_type_4817_);
                    crate::leanh::lean_dec_ref(v_logOnUnused_4809_);
                    crate::leanh::lean_dec_ref(v_p_4808_);
                    v___x_4827_ = crate::leanh::lean_box(0);
                    if v_isShared_4822_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4821_, 0, v___x_4827_);
                        v___x_4829_ = v___x_4821_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4830_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4830_, 0, v___x_4827_);
                        v___x_4829_ = v_reuseFailAlloc_4830_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4831_ = l_Lean_Expr_hasSorry(v_type_4817_);
                    if v___x_4831_ == 0 {
                        crate::leanh::lean_del_object(v___x_4821_);
                        v___x_4832_ = crate::leanh::lean_box((v___x_4831_) as usize);
                        crate::leanh::lean_inc(v_a_4819_);
                        crate::leanh::lean_inc_ref(v_type_4817_);
                        v___f_4833_ = crate::leanh::lean_alloc_closure(l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere___lam__0___boxed as *mut core::ffi::c_void, 14, 5);
                        crate::leanh::lean_closure_set(v___f_4833_, 0, v_p_4808_);
                        crate::leanh::lean_closure_set(v___f_4833_, 1, v_type_4817_);
                        crate::leanh::lean_closure_set(v___f_4833_, 2, v_a_4819_);
                        crate::leanh::lean_closure_set(v___f_4833_, 3, v___x_4832_);
                        crate::leanh::lean_closure_set(v___f_4833_, 4, v_logOnUnused_4809_);
                        v___x_4834_ = lean_array_fget(v_a_4819_, v___x_4825_);
                        crate::leanh::lean_dec(v___x_4825_);
                        crate::leanh::lean_dec(v_a_4819_);
                        v___x_4835_ = lean_nat_add(v___x_4834_, v___x_4824_);
                        crate::leanh::lean_dec(v___x_4834_);
                        v___x_4836_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4836_, 0, v___x_4835_);
                        v___x_4837_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__2___redArg(v_type_4817_, v___x_4836_, v___f_4833_, v___x_4826_, v___x_4831_, v_a_4810_, v_a_4811_, v_a_4812_, v_a_4813_, v_a_4814_, v_a_4815_);
                        return v___x_4837_;
                    } else {
                        crate::leanh::lean_dec(v___x_4825_);
                        crate::leanh::lean_dec(v_a_4819_);
                        crate::leanh::lean_dec_ref(v_type_4817_);
                        crate::leanh::lean_dec_ref(v_logOnUnused_4809_);
                        crate::leanh::lean_dec_ref(v_p_4808_);
                        v___x_4838_ = crate::leanh::lean_box(0);
                        if v_isShared_4822_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4821_, 0, v___x_4838_);
                            v___x_4840_ = v___x_4821_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4841_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4841_, 0, v___x_4838_);
                            v___x_4840_ = v_reuseFailAlloc_4841_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4829_;
            }
            3 => {
                return v___x_4840_;
            }
            4 => {
                if v_isShared_4846_ == 0 {
                    v___x_4848_ = v___x_4845_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4849_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4849_, 0, v_a_4843_);
                    v___x_4848_ = v_reuseFailAlloc_4849_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4848_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere___boxed(
    mut v_decl_4851_: *mut crate::leanh::LeanObject,
    mut v_p_4852_: *mut crate::leanh::LeanObject,
    mut v_logOnUnused_4853_: *mut crate::leanh::LeanObject,
    mut v_a_4854_: *mut crate::leanh::LeanObject,
    mut v_a_4855_: *mut crate::leanh::LeanObject,
    mut v_a_4856_: *mut crate::leanh::LeanObject,
    mut v_a_4857_: *mut crate::leanh::LeanObject,
    mut v_a_4858_: *mut crate::leanh::LeanObject,
    mut v_a_4859_: *mut crate::leanh::LeanObject,
    mut v_a_4860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4861_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere(v_decl_4851_, v_p_4852_, v_logOnUnused_4853_, v_a_4854_, v_a_4855_, v_a_4856_, v_a_4857_, v_a_4858_, v_a_4859_);
    crate::leanh::lean_dec(v_a_4859_);
    crate::leanh::lean_dec_ref(v_a_4858_);
    crate::leanh::lean_dec(v_a_4857_);
    crate::leanh::lean_dec_ref(v_a_4856_);
    crate::leanh::lean_dec(v_a_4855_);
    crate::leanh::lean_dec_ref(v_a_4854_);
    return v_res_4861_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1(
    mut v___x_4862_: *mut crate::leanh::LeanObject,
    mut v___x_4863_: u8,
    mut v_fvars_4864_: *mut crate::leanh::LeanObject,
    mut v_sz_4865_: usize,
    mut v_i_4866_: usize,
    mut v_bs_4867_: *mut crate::leanh::LeanObject,
    mut v___y_4868_: *mut crate::leanh::LeanObject,
    mut v___y_4869_: *mut crate::leanh::LeanObject,
    mut v___y_4870_: *mut crate::leanh::LeanObject,
    mut v___y_4871_: *mut crate::leanh::LeanObject,
    mut v___y_4872_: *mut crate::leanh::LeanObject,
    mut v___y_4873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4875_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1___redArg(v___x_4862_, v___x_4863_, v_fvars_4864_, v_sz_4865_, v_i_4866_, v_bs_4867_, v___y_4870_, v___y_4871_, v___y_4872_, v___y_4873_);
    return v___x_4875_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1___boxed(
    mut v___x_4876_: *mut crate::leanh::LeanObject,
    mut v___x_4877_: *mut crate::leanh::LeanObject,
    mut v_fvars_4878_: *mut crate::leanh::LeanObject,
    mut v_sz_4879_: *mut crate::leanh::LeanObject,
    mut v_i_4880_: *mut crate::leanh::LeanObject,
    mut v_bs_4881_: *mut crate::leanh::LeanObject,
    mut v___y_4882_: *mut crate::leanh::LeanObject,
    mut v___y_4883_: *mut crate::leanh::LeanObject,
    mut v___y_4884_: *mut crate::leanh::LeanObject,
    mut v___y_4885_: *mut crate::leanh::LeanObject,
    mut v___y_4886_: *mut crate::leanh::LeanObject,
    mut v___y_4887_: *mut crate::leanh::LeanObject,
    mut v___y_4888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3717__boxed_4889_: u8 = 0;
    let mut v_sz_boxed_4890_: usize = 0;
    let mut v_i_boxed_4891_: usize = 0;
    let mut v_res_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3717__boxed_4889_ = (crate::leanh::lean_unbox(v___x_4877_) as u8);
    v_sz_boxed_4890_ = crate::leanh::lean_unbox_usize(v_sz_4879_);
    crate::leanh::lean_dec(v_sz_4879_);
    v_i_boxed_4891_ = crate::leanh::lean_unbox_usize(v_i_4880_);
    crate::leanh::lean_dec(v_i_4880_);
    v_res_4892_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere_spec__1(v___x_4876_, v___x_3717__boxed_4889_, v_fvars_4878_, v_sz_boxed_4890_, v_i_boxed_4891_, v_bs_4881_, v___y_4882_, v___y_4883_, v___y_4884_, v___y_4885_, v___y_4886_, v___y_4887_);
    crate::leanh::lean_dec(v___y_4887_);
    crate::leanh::lean_dec_ref(v___y_4886_);
    crate::leanh::lean_dec(v___y_4885_);
    crate::leanh::lean_dec_ref(v___y_4884_);
    crate::leanh::lean_dec(v___y_4883_);
    crate::leanh::lean_dec_ref(v___y_4882_);
    crate::leanh::lean_dec_ref(v_fvars_4878_);
    crate::leanh::lean_dec_ref(v___x_4876_);
    return v_res_4892_;
}
pub unsafe fn l_List_filterMapTR_go___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems_spec__0(
    mut v_env_4893_: *mut crate::leanh::LeanObject,
    mut v_a_4894_: *mut crate::leanh::LeanObject,
    mut v_a_4895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: u8 = 0;
    let mut v___x_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4894_) == 0 {
                    crate::leanh::lean_dec_ref(v_env_4893_);
                    v___x_4896_ = lean_array_to_list(v_a_4895_);
                    return v___x_4896_;
                } else {
                    v_head_4897_ = crate::leanh::lean_ctor_get(v_a_4894_, 0);
                    crate::leanh::lean_inc(v_head_4897_);
                    v_tail_4898_ = crate::leanh::lean_ctor_get(v_a_4894_, 1);
                    crate::leanh::lean_inc(v_tail_4898_);
                    crate::leanh::lean_dec_ref_known(v_a_4894_, 2);
                    v___x_4899_ = 0;
                    crate::leanh::lean_inc_ref(v_env_4893_);
                    v___x_4900_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Environment_findTheoremConstVal_x3f(v_env_4893_, v_head_4897_, v___x_4899_);
                    if crate::leanh::lean_obj_tag(v___x_4900_) == 0 {
                        v_a_4894_ = v_tail_4898_;
                        state = 0;
                        continue;
                    } else {
                        v_val_4902_ = crate::leanh::lean_ctor_get(v___x_4900_, 0);
                        crate::leanh::lean_inc(v_val_4902_);
                        crate::leanh::lean_dec_ref_known(v___x_4900_, 1);
                        v___x_4903_ = lean_array_push(v_a_4895_, v_val_4902_);
                        v_a_4894_ = v_tail_4898_;
                        v_a_4895_ = v___x_4903_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems(
    mut v_t_4907_: *mut crate::leanh::LeanObject,
    mut v_env_4908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4909_ = l_Lean_Linter_getDeclsByBody(v_t_4907_);
    v___x_4910_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems___closed__0;
    v___x_4911_ = l_List_filterMapTR_go___at___00__private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems_spec__0(v_env_4908_, v___x_4909_, v___x_4910_);
    return v___x_4911_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0(
    mut v_n_4930_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_4932_: u8 = 0;
    let mut v___x_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: u8 = 0;
    let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: u8 = 0;
    let mut v___x_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: u8 = 0;
    let mut v___x_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: u8 = 0;
    let mut v___x_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: u8 = 0;
    let mut v___x_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4941_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__9;
                v___x_4942_ = lean_name_eq(v_n_4930_, v___x_4941_);
                if v___x_4942_ == 0 {
                    v___x_4943_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__11;
                    v___x_4944_ = lean_name_eq(v_n_4930_, v___x_4943_);
                    v___y_4932_ = v___x_4944_;
                    state = 1;
                    continue;
                } else {
                    v___y_4932_ = v___x_4942_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_4932_ == 0 {
                    v___x_4933_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__1;
                    v___x_4934_ = lean_name_eq(v_n_4930_, v___x_4933_);
                    if v___x_4934_ == 0 {
                        v___x_4935_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__3;
                        v___x_4936_ = lean_name_eq(v_n_4930_, v___x_4935_);
                        if v___x_4936_ == 0 {
                            v___x_4937_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__5;
                            v___x_4938_ = lean_name_eq(v_n_4930_, v___x_4937_);
                            if v___x_4938_ == 0 {
                                v___x_4939_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__7;
                                v___x_4940_ = lean_name_eq(v_n_4930_, v___x_4939_);
                                return v___x_4940_;
                            } else {
                                return v___x_4938_;
                            }
                        } else {
                            return v___x_4936_;
                        }
                    } else {
                        return v___x_4934_;
                    }
                } else {
                    return v___y_4932_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___boxed(
    mut v_n_4945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4946_: u8 = 0;
    let mut v_r_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4946_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0(v_n_4945_);
    crate::leanh::lean_dec(v_n_4945_);
    v_r_4947_ = crate::leanh::lean_box((v_res_4946_) as usize);
    return v_r_4947_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant(
    mut v_type_4949_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___f_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: u8 = 0;
    v___f_4950_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___closed__0;
    v___x_4951_ =
        l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_isAppOrForallOfConstP(
            v___f_4950_,
            v_type_4949_,
        );
    return v___x_4951_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___boxed(
    mut v_type_4952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4953_: u8 = 0;
    let mut v_r_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4953_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant(v_type_4952_);
    v_r_4954_ = crate::leanh::lean_box((v_res_4953_) as usize);
    return v_r_4954_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1___redArg(
    mut v___y_4955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4957_ = lean_st_ref_get(v___y_4955_);
    v_infoState_4958_ = crate::leanh::lean_ctor_get(v___x_4957_, 8);
    crate::leanh::lean_inc_ref(v_infoState_4958_);
    crate::leanh::lean_dec(v___x_4957_);
    v_trees_4959_ = crate::leanh::lean_ctor_get(v_infoState_4958_, 2);
    crate::leanh::lean_inc_ref(v_trees_4959_);
    crate::leanh::lean_dec_ref(v_infoState_4958_);
    v___x_4960_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4960_, 0, v_trees_4959_);
    return v___x_4960_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1___redArg___boxed(
    mut v___y_4961_: *mut crate::leanh::LeanObject,
    mut v___y_4962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4963_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1___redArg(v___y_4961_);
    crate::leanh::lean_dec(v___y_4961_);
    return v_res_4963_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1(
    mut v___y_4964_: *mut crate::leanh::LeanObject,
    mut v___y_4965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4967_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1___redArg(v___y_4965_);
    return v___x_4967_;
}
pub unsafe fn l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1___boxed(
    mut v___y_4968_: *mut crate::leanh::LeanObject,
    mut v___y_4969_: *mut crate::leanh::LeanObject,
    mut v___y_4970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4971_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1(v___y_4968_, v___y_4969_);
    crate::leanh::lean_dec(v___y_4969_);
    crate::leanh::lean_dec_ref(v___y_4968_);
    return v_res_4971_;
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2(
    mut v___x_4973_: u8,
    mut v_a_4974_: *mut crate::leanh::LeanObject,
    mut v_a_4975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4981_: u8 = 0;
    let mut v___y_4983_: u8 = 0;
    let mut v___x_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: u8 = 0;
    let mut v___x_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: u8 = 0;
    let mut v_isSharedCheck_4996_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4974_) == 0 {
                    v___x_4976_ = l_List_reverse___redArg(v_a_4975_);
                    return v___x_4976_;
                } else {
                    v_head_4977_ = crate::leanh::lean_ctor_get(v_a_4974_, 0);
                    v_tail_4978_ = crate::leanh::lean_ctor_get(v_a_4974_, 1);
                    v_isSharedCheck_4996_ = (!crate::leanh::lean_is_exclusive(v_a_4974_)) as u8;
                    if v_isSharedCheck_4996_ == 0 {
                        v___x_4980_ = v_a_4974_;
                        v_isShared_4981_ = v_isSharedCheck_4996_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4978_);
                        crate::leanh::lean_inc(v_head_4977_);
                        crate::leanh::lean_dec(v_a_4974_);
                        v___x_4980_ = crate::leanh::lean_box(0);
                        v_isShared_4981_ = v_isSharedCheck_4996_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_name_4989_ = crate::leanh::lean_ctor_get(v_head_4977_, 0);
                v_type_4990_ = crate::leanh::lean_ctor_get(v_head_4977_, 2);
                v___x_4991_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_isDecidableVariant___lam__0___closed__9;
                crate::leanh::lean_inc(v_name_4989_);
                v___x_4992_ = l_Lean_privateToUserName(v_name_4989_);
                v___x_4993_ = l_Lean_Name_isPrefixOf(v___x_4991_, v___x_4992_);
                crate::leanh::lean_dec(v___x_4992_);
                if v___x_4993_ == 0 {
                    v___x_4994_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2___closed__0;
                    crate::leanh::lean_inc_ref(v_type_4990_);
                    v___x_4995_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Expr_hasInstanceBinderOf(v___x_4994_, v_type_4990_);
                    v___y_4983_ = v___x_4995_;
                    state = 2;
                    continue;
                } else {
                    v___y_4983_ = v___x_4973_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_4983_ == 0 {
                    crate::leanh::lean_del_object(v___x_4980_);
                    crate::leanh::lean_dec(v_head_4977_);
                    v_a_4974_ = v_tail_4978_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_4981_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4980_, 1, v_a_4975_);
                        v___x_4986_ = v___x_4980_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4988_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4988_, 0, v_head_4977_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4988_, 1, v_a_4975_);
                        v___x_4986_ = v_reuseFailAlloc_4988_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v_a_4974_ = v_tail_4978_;
                v_a_4975_ = v___x_4986_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2___boxed(
    mut v___x_4997_: *mut crate::leanh::LeanObject,
    mut v_a_4998_: *mut crate::leanh::LeanObject,
    mut v_a_4999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_12523__boxed_5000_: u8 = 0;
    let mut v_res_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_12523__boxed_5000_ = (crate::leanh::lean_unbox(v___x_4997_) as u8);
    v_res_5001_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2(v___x_12523__boxed_5000_, v_a_4998_, v_a_4999_);
    return v_res_5001_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__4_spec__5___redArg(
    mut v_o_5002_: *mut crate::leanh::LeanObject,
    mut v___y_5003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_linterSets_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5005_ = lean_st_ref_get(v___y_5003_);
    v_env_5006_ = crate::leanh::lean_ctor_get(v___x_5005_, 0);
    crate::leanh::lean_inc_ref(v_env_5006_);
    crate::leanh::lean_dec(v___x_5005_);
    v___x_5007_ = l_Lean_Linter_linterSetsExt;
    v_toEnvExtension_5008_ = crate::leanh::lean_ctor_get(v___x_5007_, 0);
    v_asyncMode_5009_ = crate::leanh::lean_ctor_get(v_toEnvExtension_5008_, 2);
    v___x_5010_ = crate::leanh::lean_box(1);
    v___x_5011_ = crate::leanh::lean_box(0);
    v_linterSets_5012_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_5010_,
        v___x_5007_,
        v_env_5006_,
        v_asyncMode_5009_,
        v___x_5011_,
    );
    v___x_5013_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5013_, 0, v_o_5002_);
    crate::leanh::lean_ctor_set(v___x_5013_, 1, v_linterSets_5012_);
    v___x_5014_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5014_, 0, v___x_5013_);
    return v___x_5014_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__4_spec__5___redArg___boxed(
    mut v_o_5015_: *mut crate::leanh::LeanObject,
    mut v___y_5016_: *mut crate::leanh::LeanObject,
    mut v___y_5017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5018_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__4_spec__5___redArg(v_o_5015_, v___y_5016_);
    crate::leanh::lean_dec(v___y_5016_);
    return v_res_5018_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__4(
    mut v___y_5019_: *mut crate::leanh::LeanObject,
    mut v___y_5020_: *mut crate::leanh::LeanObject,
    mut v___y_5021_: *mut crate::leanh::LeanObject,
    mut v___y_5022_: *mut crate::leanh::LeanObject,
    mut v___y_5023_: *mut crate::leanh::LeanObject,
    mut v___y_5024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_options_5026_ = crate::leanh::lean_ctor_get(v___y_5023_, 2);
    crate::leanh::lean_inc_ref(v_options_5026_);
    v___x_5027_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__4_spec__5___redArg(v_options_5026_, v___y_5024_);
    return v___x_5027_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__4___boxed(
    mut v___y_5028_: *mut crate::leanh::LeanObject,
    mut v___y_5029_: *mut crate::leanh::LeanObject,
    mut v___y_5030_: *mut crate::leanh::LeanObject,
    mut v___y_5031_: *mut crate::leanh::LeanObject,
    mut v___y_5032_: *mut crate::leanh::LeanObject,
    mut v___y_5033_: *mut crate::leanh::LeanObject,
    mut v___y_5034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5035_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__4(v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_);
    crate::leanh::lean_dec(v___y_5033_);
    crate::leanh::lean_dec_ref(v___y_5032_);
    crate::leanh::lean_dec(v___y_5031_);
    crate::leanh::lean_dec_ref(v___y_5030_);
    crate::leanh::lean_dec(v___y_5029_);
    crate::leanh::lean_dec_ref(v___y_5028_);
    return v_res_5035_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10_spec__13(
    mut v_msgData_5036_: *mut crate::leanh::LeanObject,
    mut v___y_5037_: *mut crate::leanh::LeanObject,
    mut v___y_5038_: *mut crate::leanh::LeanObject,
    mut v___y_5039_: *mut crate::leanh::LeanObject,
    mut v___y_5040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5042_ = lean_st_ref_get(v___y_5040_);
    v_env_5043_ = crate::leanh::lean_ctor_get(v___x_5042_, 0);
    crate::leanh::lean_inc_ref(v_env_5043_);
    crate::leanh::lean_dec(v___x_5042_);
    v___x_5044_ = lean_st_ref_get(v___y_5038_);
    v_mctx_5045_ = crate::leanh::lean_ctor_get(v___x_5044_, 0);
    crate::leanh::lean_inc_ref(v_mctx_5045_);
    crate::leanh::lean_dec(v___x_5044_);
    v_lctx_5046_ = crate::leanh::lean_ctor_get(v___y_5037_, 2);
    v_options_5047_ = crate::leanh::lean_ctor_get(v___y_5039_, 2);
    crate::leanh::lean_inc_ref(v_options_5047_);
    crate::leanh::lean_inc_ref(v_lctx_5046_);
    v___x_5048_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5048_, 0, v_env_5043_);
    crate::leanh::lean_ctor_set(v___x_5048_, 1, v_mctx_5045_);
    crate::leanh::lean_ctor_set(v___x_5048_, 2, v_lctx_5046_);
    crate::leanh::lean_ctor_set(v___x_5048_, 3, v_options_5047_);
    v___x_5049_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5049_, 0, v___x_5048_);
    crate::leanh::lean_ctor_set(v___x_5049_, 1, v_msgData_5036_);
    v___x_5050_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5050_, 0, v___x_5049_);
    return v___x_5050_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10_spec__13___boxed(
    mut v_msgData_5051_: *mut crate::leanh::LeanObject,
    mut v___y_5052_: *mut crate::leanh::LeanObject,
    mut v___y_5053_: *mut crate::leanh::LeanObject,
    mut v___y_5054_: *mut crate::leanh::LeanObject,
    mut v___y_5055_: *mut crate::leanh::LeanObject,
    mut v___y_5056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5057_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10_spec__13(v_msgData_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_);
    crate::leanh::lean_dec(v___y_5055_);
    crate::leanh::lean_dec_ref(v___y_5054_);
    crate::leanh::lean_dec(v___y_5053_);
    crate::leanh::lean_dec_ref(v___y_5052_);
    return v_res_5057_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0(
    mut v___y_5066_: u8,
    mut v_suppressElabErrors_5067_: u8,
    mut v_x_5068_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_5068_) == 1 {
        let mut v_pre_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_5069_ = crate::leanh::lean_ctor_get(v_x_5068_, 0);
        match crate::leanh::lean_obj_tag(v_pre_5069_) {
            1 => {
                let mut v_pre_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_5070_ = crate::leanh::lean_ctor_get(v_pre_5069_, 0);
                match crate::leanh::lean_obj_tag(v_pre_5070_) {
                    0 => {
                        let mut v_str_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5074_: u8 = 0;
                        v_str_5071_ = crate::leanh::lean_ctor_get(v_x_5068_, 1);
                        v_str_5072_ = crate::leanh::lean_ctor_get(v_pre_5069_, 1);
                        v___x_5073_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__0;
                        v___x_5074_ = lean_string_dec_eq(v_str_5072_, v___x_5073_);
                        if v___x_5074_ == 0 {
                            let mut v___x_5075_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_5076_: u8 = 0;
                            v___x_5075_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__1;
                            v___x_5076_ = lean_string_dec_eq(v_str_5072_, v___x_5075_);
                            if v___x_5076_ == 0 {
                                return v___y_5066_;
                            } else {
                                let mut v___x_5077_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_5078_: u8 = 0;
                                v___x_5077_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__2;
                                v___x_5078_ = lean_string_dec_eq(v_str_5071_, v___x_5077_);
                                if v___x_5078_ == 0 {
                                    return v___y_5066_;
                                } else {
                                    return v_suppressElabErrors_5067_;
                                }
                            }
                        } else {
                            let mut v___x_5079_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_5080_: u8 = 0;
                            v___x_5079_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__3;
                            v___x_5080_ = lean_string_dec_eq(v_str_5071_, v___x_5079_);
                            if v___x_5080_ == 0 {
                                return v___y_5066_;
                            } else {
                                return v_suppressElabErrors_5067_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_5081_ = crate::leanh::lean_ctor_get(v_pre_5070_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_5081_) == 0 {
                            let mut v_str_5082_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_5083_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_5084_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_5085_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_5086_: u8 = 0;
                            v_str_5082_ = crate::leanh::lean_ctor_get(v_x_5068_, 1);
                            v_str_5083_ = crate::leanh::lean_ctor_get(v_pre_5069_, 1);
                            v_str_5084_ = crate::leanh::lean_ctor_get(v_pre_5070_, 1);
                            v___x_5085_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__4;
                            v___x_5086_ = lean_string_dec_eq(v_str_5084_, v___x_5085_);
                            if v___x_5086_ == 0 {
                                return v___y_5066_;
                            } else {
                                let mut v___x_5087_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_5088_: u8 = 0;
                                v___x_5087_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__5;
                                v___x_5088_ = lean_string_dec_eq(v_str_5083_, v___x_5087_);
                                if v___x_5088_ == 0 {
                                    return v___y_5066_;
                                } else {
                                    let mut v___x_5089_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_5090_: u8 = 0;
                                    v___x_5089_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__6;
                                    v___x_5090_ = lean_string_dec_eq(v_str_5082_, v___x_5089_);
                                    if v___x_5090_ == 0 {
                                        return v___y_5066_;
                                    } else {
                                        return v_suppressElabErrors_5067_;
                                    }
                                }
                            }
                        } else {
                            return v___y_5066_;
                        }
                    }
                    _ => {
                        return v___y_5066_;
                    }
                }
            }
            0 => {
                let mut v_str_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5093_: u8 = 0;
                v_str_5091_ = crate::leanh::lean_ctor_get(v_x_5068_, 1);
                v___x_5092_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___closed__7;
                v___x_5093_ = lean_string_dec_eq(v_str_5091_, v___x_5092_);
                if v___x_5093_ == 0 {
                    return v___y_5066_;
                } else {
                    return v_suppressElabErrors_5067_;
                }
            }
            _ => {
                return v___y_5066_;
            }
        }
    } else {
        return v___y_5066_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___boxed(
    mut v___y_5094_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_5095_: *mut crate::leanh::LeanObject,
    mut v_x_5096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_12653__boxed_5097_: u8 = 0;
    let mut v_suppressElabErrors_boxed_5098_: u8 = 0;
    let mut v_res_5099_: u8 = 0;
    let mut v_r_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_12653__boxed_5097_ = (crate::leanh::lean_unbox(v___y_5094_) as u8);
    v_suppressElabErrors_boxed_5098_ = (crate::leanh::lean_unbox(v_suppressElabErrors_5095_) as u8);
    v_res_5099_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0(v___y_12653__boxed_5097_, v_suppressElabErrors_boxed_5098_, v_x_5096_);
    crate::leanh::lean_dec(v_x_5096_);
    v_r_5100_ = crate::leanh::lean_box((v_res_5099_) as usize);
    return v_r_5100_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10_spec__14(
    mut v_opts_5101_: *mut crate::leanh::LeanObject,
    mut v_opt_5102_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_5103_ = crate::leanh::lean_ctor_get(v_opt_5102_, 0);
    v_defValue_5104_ = crate::leanh::lean_ctor_get(v_opt_5102_, 1);
    v_map_5105_ = crate::leanh::lean_ctor_get(v_opts_5101_, 0);
    v___x_5106_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_5105_,
            v_name_5103_,
        );
    if crate::leanh::lean_obj_tag(v___x_5106_) == 0 {
        let mut v___x_5107_: u8 = 0;
        v___x_5107_ = (crate::leanh::lean_unbox(v_defValue_5104_) as u8);
        return v___x_5107_;
    } else {
        let mut v_val_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_5108_ = crate::leanh::lean_ctor_get(v___x_5106_, 0);
        crate::leanh::lean_inc(v_val_5108_);
        crate::leanh::lean_dec_ref_known(v___x_5106_, 1);
        if crate::leanh::lean_obj_tag(v_val_5108_) == 1 {
            let mut v_v_5109_: u8 = 0;
            v_v_5109_ = crate::leanh::lean_ctor_get_uint8(v_val_5108_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_5108_, 0);
            return v_v_5109_;
        } else {
            let mut v___x_5110_: u8 = 0;
            crate::leanh::lean_dec(v_val_5108_);
            v___x_5110_ = (crate::leanh::lean_unbox(v_defValue_5104_) as u8);
            return v___x_5110_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10_spec__14___boxed(
    mut v_opts_5111_: *mut crate::leanh::LeanObject,
    mut v_opt_5112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5113_: u8 = 0;
    let mut v_r_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5113_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10_spec__14(v_opts_5111_, v_opt_5112_);
    crate::leanh::lean_dec_ref(v_opt_5112_);
    crate::leanh::lean_dec_ref(v_opts_5111_);
    v_r_5114_ = crate::leanh::lean_box((v_res_5113_) as usize);
    return v_r_5114_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg(
    mut v_ref_5115_: *mut crate::leanh::LeanObject,
    mut v_msgData_5116_: *mut crate::leanh::LeanObject,
    mut v_severity_5117_: u8,
    mut v_isSilent_5118_: u8,
    mut v___y_5119_: *mut crate::leanh::LeanObject,
    mut v___y_5120_: *mut crate::leanh::LeanObject,
    mut v___y_5121_: *mut crate::leanh::LeanObject,
    mut v___y_5122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5127_: u8 = 0;
    let mut v___y_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5129_: u8 = 0;
    let mut v___y_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5148_: u8 = 0;
    let mut v___x_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5159_: u8 = 0;
    let mut v___y_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5163_: u8 = 0;
    let mut v___y_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5165_: u8 = 0;
    let mut v___y_5166_: u8 = 0;
    let mut v___y_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5174_: u8 = 0;
    let mut v___x_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: u8 = 0;
    let mut v___x_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5184_: u8 = 0;
    let mut v___y_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5188_: u8 = 0;
    let mut v___y_5189_: u8 = 0;
    let mut v___y_5190_: u8 = 0;
    let mut v___y_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5198_: u8 = 0;
    let mut v___y_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5200_: u8 = 0;
    let mut v___y_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5203_: u8 = 0;
    let mut v_ref_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5208_: u8 = 0;
    let mut v___y_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5211_: u8 = 0;
    let mut v___y_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5215_: u8 = 0;
    let mut v___y_5216_: u8 = 0;
    let mut v___y_5218_: u8 = 0;
    let mut v_fileName_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5223_: u8 = 0;
    let mut v___x_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: u8 = 0;
    let mut v___x_5228_: u8 = 0;
    let mut v___x_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: u8 = 0;
    let mut v___x_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: u8 = 0;
    let mut v___x_5234_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5208_ = 2;
                v___x_5233_ = l_Lean_instBEqMessageSeverity_beq(v_severity_5117_, v___x_5208_);
                if v___x_5233_ == 0 {
                    v___y_5218_ = v___x_5233_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_5116_);
                    v___x_5234_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_5116_);
                    v___y_5218_ = v___x_5234_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_5134_ = lean_st_ref_take(v___y_5133_);
                v_currNamespace_5135_ = crate::leanh::lean_ctor_get(v___y_5132_, 6);
                v_openDecls_5136_ = crate::leanh::lean_ctor_get(v___y_5132_, 7);
                v_env_5137_ = crate::leanh::lean_ctor_get(v___x_5134_, 0);
                v_nextMacroScope_5138_ = crate::leanh::lean_ctor_get(v___x_5134_, 1);
                v_ngen_5139_ = crate::leanh::lean_ctor_get(v___x_5134_, 2);
                v_auxDeclNGen_5140_ = crate::leanh::lean_ctor_get(v___x_5134_, 3);
                v_traceState_5141_ = crate::leanh::lean_ctor_get(v___x_5134_, 4);
                v_cache_5142_ = crate::leanh::lean_ctor_get(v___x_5134_, 5);
                v_messages_5143_ = crate::leanh::lean_ctor_get(v___x_5134_, 6);
                v_infoState_5144_ = crate::leanh::lean_ctor_get(v___x_5134_, 7);
                v_snapshotTasks_5145_ = crate::leanh::lean_ctor_get(v___x_5134_, 8);
                v_isSharedCheck_5159_ = (!crate::leanh::lean_is_exclusive(v___x_5134_)) as u8;
                if v_isSharedCheck_5159_ == 0 {
                    v___x_5147_ = v___x_5134_;
                    v_isShared_5148_ = v_isSharedCheck_5159_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5145_);
                    crate::leanh::lean_inc(v_infoState_5144_);
                    crate::leanh::lean_inc(v_messages_5143_);
                    crate::leanh::lean_inc(v_cache_5142_);
                    crate::leanh::lean_inc(v_traceState_5141_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5140_);
                    crate::leanh::lean_inc(v_ngen_5139_);
                    crate::leanh::lean_inc(v_nextMacroScope_5138_);
                    crate::leanh::lean_inc(v_env_5137_);
                    crate::leanh::lean_dec(v___x_5134_);
                    v___x_5147_ = crate::leanh::lean_box(0);
                    v_isShared_5148_ = v_isSharedCheck_5159_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_5136_);
                crate::leanh::lean_inc(v_currNamespace_5135_);
                v___x_5149_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5149_, 0, v_currNamespace_5135_);
                crate::leanh::lean_ctor_set(v___x_5149_, 1, v_openDecls_5136_);
                v___x_5150_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5150_, 0, v___x_5149_);
                crate::leanh::lean_ctor_set(v___x_5150_, 1, v___y_5131_);
                crate::leanh::lean_inc_ref(v___y_5130_);
                crate::leanh::lean_inc_ref(v___y_5126_);
                v___x_5151_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_5151_, 0, v___y_5126_);
                crate::leanh::lean_ctor_set(v___x_5151_, 1, v___y_5125_);
                crate::leanh::lean_ctor_set(v___x_5151_, 2, v___y_5128_);
                crate::leanh::lean_ctor_set(v___x_5151_, 3, v___y_5130_);
                crate::leanh::lean_ctor_set(v___x_5151_, 4, v___x_5150_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5151_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_5127_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5151_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_5129_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5151_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_5118_,
                );
                v___x_5152_ = l_Lean_MessageLog_add(v___x_5151_, v_messages_5143_);
                if v_isShared_5148_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5147_, 6, v___x_5152_);
                    v___x_5154_ = v___x_5147_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5158_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5158_, 0, v_env_5137_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5158_, 1, v_nextMacroScope_5138_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5158_, 2, v_ngen_5139_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5158_, 3, v_auxDeclNGen_5140_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5158_, 4, v_traceState_5141_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5158_, 5, v_cache_5142_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5158_, 6, v___x_5152_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5158_, 7, v_infoState_5144_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5158_, 8, v_snapshotTasks_5145_);
                    v___x_5154_ = v_reuseFailAlloc_5158_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5155_ = lean_st_ref_set(v___y_5133_, v___x_5154_);
                v___x_5156_ = crate::leanh::lean_box(0);
                v___x_5157_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5157_, 0, v___x_5156_);
                return v___x_5157_;
            }
            4 => {
                v___x_5169_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_5116_,
                    );
                v___x_5170_ = l_Lean_addMessageContextFull___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10_spec__13(v___x_5169_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_);
                v_a_5171_ = crate::leanh::lean_ctor_get(v___x_5170_, 0);
                v_isSharedCheck_5184_ = (!crate::leanh::lean_is_exclusive(v___x_5170_)) as u8;
                if v_isSharedCheck_5184_ == 0 {
                    v___x_5173_ = v___x_5170_;
                    v_isShared_5174_ = v_isSharedCheck_5184_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5171_);
                    crate::leanh::lean_dec(v___x_5170_);
                    v___x_5173_ = crate::leanh::lean_box(0);
                    v_isShared_5174_ = v_isSharedCheck_5184_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_5167_, 2);
                v___x_5175_ = l_Lean_FileMap_toPosition(v___y_5167_, v___y_5162_);
                crate::leanh::lean_dec(v___y_5162_);
                v___x_5176_ = l_Lean_FileMap_toPosition(v___y_5167_, v___y_5168_);
                crate::leanh::lean_dec(v___y_5168_);
                v___x_5177_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5177_, 0, v___x_5176_);
                v___x_5178_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg___closed__4;
                if v___y_5163_ == 0 {
                    crate::leanh::lean_del_object(v___x_5173_);
                    crate::leanh::lean_dec_ref(v___y_5161_);
                    v___y_5125_ = v___x_5175_;
                    v___y_5126_ = v___y_5164_;
                    v___y_5127_ = v___y_5165_;
                    v___y_5128_ = v___x_5177_;
                    v___y_5129_ = v___y_5166_;
                    v___y_5130_ = v___x_5178_;
                    v___y_5131_ = v_a_5171_;
                    v___y_5132_ = v___y_5121_;
                    v___y_5133_ = v___y_5122_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5171_);
                    v___x_5179_ = l_Lean_MessageData_hasTag(v___y_5161_, v_a_5171_);
                    if v___x_5179_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5177_, 1);
                        crate::leanh::lean_dec_ref(v___x_5175_);
                        crate::leanh::lean_dec(v_a_5171_);
                        v___x_5180_ = crate::leanh::lean_box(0);
                        if v_isShared_5174_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5173_, 0, v___x_5180_);
                            v___x_5182_ = v___x_5173_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_5183_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5183_, 0, v___x_5180_);
                            v___x_5182_ = v_reuseFailAlloc_5183_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5173_);
                        v___y_5125_ = v___x_5175_;
                        v___y_5126_ = v___y_5164_;
                        v___y_5127_ = v___y_5165_;
                        v___y_5128_ = v___x_5177_;
                        v___y_5129_ = v___y_5166_;
                        v___y_5130_ = v___x_5178_;
                        v___y_5131_ = v_a_5171_;
                        v___y_5132_ = v___y_5121_;
                        v___y_5133_ = v___y_5122_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_5182_;
            }
            7 => {
                v___x_5194_ = l_Lean_Syntax_getTailPos_x3f(v___y_5191_, v___y_5189_);
                crate::leanh::lean_dec(v___y_5191_);
                if crate::leanh::lean_obj_tag(v___x_5194_) == 0 {
                    crate::leanh::lean_inc(v___y_5193_);
                    v___y_5161_ = v___y_5186_;
                    v___y_5162_ = v___y_5193_;
                    v___y_5163_ = v___y_5188_;
                    v___y_5164_ = v___y_5187_;
                    v___y_5165_ = v___y_5189_;
                    v___y_5166_ = v___y_5190_;
                    v___y_5167_ = v___y_5192_;
                    v___y_5168_ = v___y_5193_;
                    state = 4;
                    continue;
                } else {
                    v_val_5195_ = crate::leanh::lean_ctor_get(v___x_5194_, 0);
                    crate::leanh::lean_inc(v_val_5195_);
                    crate::leanh::lean_dec_ref_known(v___x_5194_, 1);
                    v___y_5161_ = v___y_5186_;
                    v___y_5162_ = v___y_5193_;
                    v___y_5163_ = v___y_5188_;
                    v___y_5164_ = v___y_5187_;
                    v___y_5165_ = v___y_5189_;
                    v___y_5166_ = v___y_5190_;
                    v___y_5167_ = v___y_5192_;
                    v___y_5168_ = v_val_5195_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_5204_ = l_Lean_replaceRef(v_ref_5115_, v___y_5202_);
                v___x_5205_ = l_Lean_Syntax_getPos_x3f(v_ref_5204_, v___y_5200_);
                if crate::leanh::lean_obj_tag(v___x_5205_) == 0 {
                    v___x_5206_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_5186_ = v___y_5197_;
                    v___y_5187_ = v___y_5199_;
                    v___y_5188_ = v___y_5198_;
                    v___y_5189_ = v___y_5200_;
                    v___y_5190_ = v___y_5203_;
                    v___y_5191_ = v_ref_5204_;
                    v___y_5192_ = v___y_5201_;
                    v___y_5193_ = v___x_5206_;
                    state = 7;
                    continue;
                } else {
                    v_val_5207_ = crate::leanh::lean_ctor_get(v___x_5205_, 0);
                    crate::leanh::lean_inc(v_val_5207_);
                    crate::leanh::lean_dec_ref_known(v___x_5205_, 1);
                    v___y_5186_ = v___y_5197_;
                    v___y_5187_ = v___y_5199_;
                    v___y_5188_ = v___y_5198_;
                    v___y_5189_ = v___y_5200_;
                    v___y_5190_ = v___y_5203_;
                    v___y_5191_ = v_ref_5204_;
                    v___y_5192_ = v___y_5201_;
                    v___y_5193_ = v_val_5207_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_5216_ == 0 {
                    v___y_5197_ = v___y_5212_;
                    v___y_5198_ = v___y_5211_;
                    v___y_5199_ = v___y_5210_;
                    v___y_5200_ = v___y_5215_;
                    v___y_5201_ = v___y_5214_;
                    v___y_5202_ = v___y_5213_;
                    v___y_5203_ = v_severity_5117_;
                    state = 8;
                    continue;
                } else {
                    v___y_5197_ = v___y_5212_;
                    v___y_5198_ = v___y_5211_;
                    v___y_5199_ = v___y_5210_;
                    v___y_5200_ = v___y_5215_;
                    v___y_5201_ = v___y_5214_;
                    v___y_5202_ = v___y_5213_;
                    v___y_5203_ = v___x_5208_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_5218_ == 0 {
                    v_fileName_5219_ = crate::leanh::lean_ctor_get(v___y_5121_, 0);
                    v_fileMap_5220_ = crate::leanh::lean_ctor_get(v___y_5121_, 1);
                    v_options_5221_ = crate::leanh::lean_ctor_get(v___y_5121_, 2);
                    v_ref_5222_ = crate::leanh::lean_ctor_get(v___y_5121_, 5);
                    v_suppressElabErrors_5223_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_5121_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_5224_ = crate::leanh::lean_box((v___y_5218_) as usize);
                    v___x_5225_ = crate::leanh::lean_box((v_suppressElabErrors_5223_) as usize);
                    v___f_5226_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_5226_, 0, v___x_5224_);
                    crate::leanh::lean_closure_set(v___f_5226_, 1, v___x_5225_);
                    v___x_5227_ = 1;
                    v___x_5228_ = l_Lean_instBEqMessageSeverity_beq(v_severity_5117_, v___x_5227_);
                    if v___x_5228_ == 0 {
                        v___y_5210_ = v_fileName_5219_;
                        v___y_5211_ = v_suppressElabErrors_5223_;
                        v___y_5212_ = v___f_5226_;
                        v___y_5213_ = v_ref_5222_;
                        v___y_5214_ = v_fileMap_5220_;
                        v___y_5215_ = v___y_5218_;
                        v___y_5216_ = v___x_5228_;
                        state = 9;
                        continue;
                    } else {
                        v___x_5229_ = l_Lean_warningAsError;
                        v___x_5230_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10_spec__14(v_options_5221_, v___x_5229_);
                        v___y_5210_ = v_fileName_5219_;
                        v___y_5211_ = v_suppressElabErrors_5223_;
                        v___y_5212_ = v___f_5226_;
                        v___y_5213_ = v_ref_5222_;
                        v___y_5214_ = v_fileMap_5220_;
                        v___y_5215_ = v___y_5218_;
                        v___y_5216_ = v___x_5230_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_5116_);
                    v___x_5231_ = crate::leanh::lean_box(0);
                    v___x_5232_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5232_, 0, v___x_5231_);
                    return v___x_5232_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg___boxed(
    mut v_ref_5235_: *mut crate::leanh::LeanObject,
    mut v_msgData_5236_: *mut crate::leanh::LeanObject,
    mut v_severity_5237_: *mut crate::leanh::LeanObject,
    mut v_isSilent_5238_: *mut crate::leanh::LeanObject,
    mut v___y_5239_: *mut crate::leanh::LeanObject,
    mut v___y_5240_: *mut crate::leanh::LeanObject,
    mut v___y_5241_: *mut crate::leanh::LeanObject,
    mut v___y_5242_: *mut crate::leanh::LeanObject,
    mut v___y_5243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_5244_: u8 = 0;
    let mut v_isSilent_boxed_5245_: u8 = 0;
    let mut v_res_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_5244_ = (crate::leanh::lean_unbox(v_severity_5237_) as u8);
    v_isSilent_boxed_5245_ = (crate::leanh::lean_unbox(v_isSilent_5238_) as u8);
    v_res_5246_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg(v_ref_5235_, v_msgData_5236_, v_severity_boxed_5244_, v_isSilent_boxed_5245_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_);
    crate::leanh::lean_dec(v___y_5242_);
    crate::leanh::lean_dec_ref(v___y_5241_);
    crate::leanh::lean_dec(v___y_5240_);
    crate::leanh::lean_dec_ref(v___y_5239_);
    crate::leanh::lean_dec(v_ref_5235_);
    return v_res_5246_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7(
    mut v_ref_5247_: *mut crate::leanh::LeanObject,
    mut v_msgData_5248_: *mut crate::leanh::LeanObject,
    mut v___y_5249_: *mut crate::leanh::LeanObject,
    mut v___y_5250_: *mut crate::leanh::LeanObject,
    mut v___y_5251_: *mut crate::leanh::LeanObject,
    mut v___y_5252_: *mut crate::leanh::LeanObject,
    mut v___y_5253_: *mut crate::leanh::LeanObject,
    mut v___y_5254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5256_: u8 = 0;
    let mut v___x_5257_: u8 = 0;
    let mut v___x_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5256_ = 1;
    v___x_5257_ = 0;
    v___x_5258_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg(v_ref_5247_, v_msgData_5248_, v___x_5256_, v___x_5257_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_);
    return v___x_5258_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7___boxed(
    mut v_ref_5259_: *mut crate::leanh::LeanObject,
    mut v_msgData_5260_: *mut crate::leanh::LeanObject,
    mut v___y_5261_: *mut crate::leanh::LeanObject,
    mut v___y_5262_: *mut crate::leanh::LeanObject,
    mut v___y_5263_: *mut crate::leanh::LeanObject,
    mut v___y_5264_: *mut crate::leanh::LeanObject,
    mut v___y_5265_: *mut crate::leanh::LeanObject,
    mut v___y_5266_: *mut crate::leanh::LeanObject,
    mut v___y_5267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5268_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7(v_ref_5259_, v_msgData_5260_, v___y_5261_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_);
    crate::leanh::lean_dec(v___y_5266_);
    crate::leanh::lean_dec_ref(v___y_5265_);
    crate::leanh::lean_dec(v___y_5264_);
    crate::leanh::lean_dec_ref(v___y_5263_);
    crate::leanh::lean_dec(v___y_5262_);
    crate::leanh::lean_dec_ref(v___y_5261_);
    crate::leanh::lean_dec(v_ref_5259_);
    return v_res_5268_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5270_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5___closed__0;
    v___x_5271_ = l_Lean_stringToMessageData(v___x_5270_);
    return v___x_5271_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5273_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5___closed__2;
    v___x_5274_ = l_Lean_stringToMessageData(v___x_5273_);
    return v___x_5274_;
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5(
    mut v_linterOption_5275_: *mut crate::leanh::LeanObject,
    mut v_stx_5276_: *mut crate::leanh::LeanObject,
    mut v_msg_5277_: *mut crate::leanh::LeanObject,
    mut v___y_5278_: *mut crate::leanh::LeanObject,
    mut v___y_5279_: *mut crate::leanh::LeanObject,
    mut v___y_5280_: *mut crate::leanh::LeanObject,
    mut v___y_5281_: *mut crate::leanh::LeanObject,
    mut v___y_5282_: *mut crate::leanh::LeanObject,
    mut v___y_5283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5288_: u8 = 0;
    let mut v___x_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_disable_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5302_: u8 = 0;
    let mut v_unused_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_5285_ = crate::leanh::lean_ctor_get(v_linterOption_5275_, 0);
                v_isSharedCheck_5302_ =
                    (!crate::leanh::lean_is_exclusive(v_linterOption_5275_)) as u8;
                if v_isSharedCheck_5302_ == 0 {
                    v_unused_5303_ = crate::leanh::lean_ctor_get(v_linterOption_5275_, 1);
                    crate::leanh::lean_dec(v_unused_5303_);
                    v___x_5287_ = v_linterOption_5275_;
                    v_isShared_5288_ = v_isSharedCheck_5302_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_name_5285_);
                    crate::leanh::lean_dec(v_linterOption_5275_);
                    v___x_5287_ = crate::leanh::lean_box(0);
                    v_isShared_5288_ = v_isSharedCheck_5302_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5289_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5___closed__1), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5___closed__1_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5___closed__1);
                crate::leanh::lean_inc(v_name_5285_);
                v___x_5290_ = l_Lean_MessageData_ofName(v_name_5285_);
                if v_isShared_5288_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5287_, 7);
                    crate::leanh::lean_ctor_set(v___x_5287_, 1, v___x_5290_);
                    crate::leanh::lean_ctor_set(v___x_5287_, 0, v___x_5289_);
                    v___x_5292_ = v___x_5287_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5301_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5301_, 0, v___x_5289_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5301_, 1, v___x_5290_);
                    v___x_5292_ = v_reuseFailAlloc_5301_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5293_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5___closed__3), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5___closed__3_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5___closed__3);
                v___x_5294_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5294_, 0, v___x_5292_);
                crate::leanh::lean_ctor_set(v___x_5294_, 1, v___x_5293_);
                v_disable_5295_ = l_Lean_MessageData_note(v___x_5294_);
                v___x_5296_ = l_Lean_Linter_linterMessageTag;
                v___x_5297_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5297_, 0, v_msg_5277_);
                crate::leanh::lean_ctor_set(v___x_5297_, 1, v_disable_5295_);
                v___x_5298_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5298_, 0, v___x_5296_);
                crate::leanh::lean_ctor_set(v___x_5298_, 1, v___x_5297_);
                v___x_5299_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5299_, 0, v_name_5285_);
                crate::leanh::lean_ctor_set(v___x_5299_, 1, v___x_5298_);
                v___x_5300_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7(v_stx_5276_, v___x_5299_, v___y_5278_, v___y_5279_, v___y_5280_, v___y_5281_, v___y_5282_, v___y_5283_);
                return v___x_5300_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5___boxed(
    mut v_linterOption_5304_: *mut crate::leanh::LeanObject,
    mut v_stx_5305_: *mut crate::leanh::LeanObject,
    mut v_msg_5306_: *mut crate::leanh::LeanObject,
    mut v___y_5307_: *mut crate::leanh::LeanObject,
    mut v___y_5308_: *mut crate::leanh::LeanObject,
    mut v___y_5309_: *mut crate::leanh::LeanObject,
    mut v___y_5310_: *mut crate::leanh::LeanObject,
    mut v___y_5311_: *mut crate::leanh::LeanObject,
    mut v___y_5312_: *mut crate::leanh::LeanObject,
    mut v___y_5313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5314_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5(v_linterOption_5304_, v_stx_5305_, v_msg_5306_, v___y_5307_, v___y_5308_, v___y_5309_, v___y_5310_, v___y_5311_, v___y_5312_);
    crate::leanh::lean_dec(v___y_5312_);
    crate::leanh::lean_dec_ref(v___y_5311_);
    crate::leanh::lean_dec(v___y_5310_);
    crate::leanh::lean_dec_ref(v___y_5309_);
    crate::leanh::lean_dec(v___y_5308_);
    crate::leanh::lean_dec_ref(v___y_5307_);
    crate::leanh::lean_dec(v_stx_5305_);
    return v_res_5314_;
}
pub unsafe fn l_Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3(
    mut v_linterOption_5315_: *mut crate::leanh::LeanObject,
    mut v_stx_5316_: *mut crate::leanh::LeanObject,
    mut v_msg_5317_: *mut crate::leanh::LeanObject,
    mut v___y_5318_: *mut crate::leanh::LeanObject,
    mut v___y_5319_: *mut crate::leanh::LeanObject,
    mut v___y_5320_: *mut crate::leanh::LeanObject,
    mut v___y_5321_: *mut crate::leanh::LeanObject,
    mut v___y_5322_: *mut crate::leanh::LeanObject,
    mut v___y_5323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5329_: u8 = 0;
    let mut v___x_5330_: u8 = 0;
    let mut v___x_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5336_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5325_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__4(v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_);
                v_a_5326_ = crate::leanh::lean_ctor_get(v___x_5325_, 0);
                v_isSharedCheck_5336_ = (!crate::leanh::lean_is_exclusive(v___x_5325_)) as u8;
                if v_isSharedCheck_5336_ == 0 {
                    v___x_5328_ = v___x_5325_;
                    v_isShared_5329_ = v_isSharedCheck_5336_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5326_);
                    crate::leanh::lean_dec(v___x_5325_);
                    v___x_5328_ = crate::leanh::lean_box(0);
                    v_isShared_5329_ = v_isSharedCheck_5336_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5330_ = l_Lean_Linter_getLinterValueExtra(v_linterOption_5315_, v_a_5326_);
                crate::leanh::lean_dec(v_a_5326_);
                if v___x_5330_ == 0 {
                    crate::leanh::lean_dec_ref(v_msg_5317_);
                    crate::leanh::lean_dec_ref(v_linterOption_5315_);
                    v___x_5331_ = crate::leanh::lean_box(0);
                    if v_isShared_5329_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5328_, 0, v___x_5331_);
                        v___x_5333_ = v___x_5328_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5334_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5334_, 0, v___x_5331_);
                        v___x_5333_ = v_reuseFailAlloc_5334_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5328_);
                    v___x_5335_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5(v_linterOption_5315_, v_stx_5316_, v_msg_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_);
                    return v___x_5335_;
                }
            }
            2 => {
                return v___x_5333_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3___boxed(
    mut v_linterOption_5337_: *mut crate::leanh::LeanObject,
    mut v_stx_5338_: *mut crate::leanh::LeanObject,
    mut v_msg_5339_: *mut crate::leanh::LeanObject,
    mut v___y_5340_: *mut crate::leanh::LeanObject,
    mut v___y_5341_: *mut crate::leanh::LeanObject,
    mut v___y_5342_: *mut crate::leanh::LeanObject,
    mut v___y_5343_: *mut crate::leanh::LeanObject,
    mut v___y_5344_: *mut crate::leanh::LeanObject,
    mut v___y_5345_: *mut crate::leanh::LeanObject,
    mut v___y_5346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5347_ = l_Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3(v_linterOption_5337_, v_stx_5338_, v_msg_5339_, v___y_5340_, v___y_5341_, v___y_5342_, v___y_5343_, v___y_5344_, v___y_5345_);
    crate::leanh::lean_dec(v___y_5345_);
    crate::leanh::lean_dec_ref(v___y_5344_);
    crate::leanh::lean_dec(v___y_5343_);
    crate::leanh::lean_dec_ref(v___y_5342_);
    crate::leanh::lean_dec(v___y_5341_);
    crate::leanh::lean_dec_ref(v___y_5340_);
    crate::leanh::lean_dec(v_stx_5338_);
    return v_res_5347_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5349_ = l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__0;
    v___x_5350_ = l_Lean_stringToMessageData(v___x_5349_);
    return v___x_5350_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5352_ = l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__2;
    v___x_5353_ = l_Lean_stringToMessageData(v___x_5352_);
    return v___x_5353_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0(
    mut v_head_5356_: *mut crate::leanh::LeanObject,
    mut v___x_5357_: *mut crate::leanh::LeanObject,
    mut v_unusedParams_5358_: *mut crate::leanh::LeanObject,
    mut v___y_5359_: *mut crate::leanh::LeanObject,
    mut v___y_5360_: *mut crate::leanh::LeanObject,
    mut v___y_5361_: *mut crate::leanh::LeanObject,
    mut v___y_5362_: *mut crate::leanh::LeanObject,
    mut v___y_5363_: *mut crate::leanh::LeanObject,
    mut v___y_5364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: u8 = 0;
    let mut v___x_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5366_ = crate::leanh::lean_ctor_get(v___y_5363_, 5);
                v_name_5367_ = crate::leanh::lean_ctor_get(v_head_5356_, 0);
                crate::leanh::lean_inc(v_name_5367_);
                crate::leanh::lean_dec_ref(v_head_5356_);
                crate::leanh::lean_inc_ref(v_unusedParams_5358_);
                v___x_5368_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_unusedInstancesMsg(v_name_5367_, v_unusedParams_5358_);
                v___x_5369_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__1_once), _init_l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__1);
                v___x_5370_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5370_, 0, v___x_5368_);
                crate::leanh::lean_ctor_set(v___x_5370_, 1, v___x_5369_);
                v___x_5378_ = lean_array_get_size(v_unusedParams_5358_);
                crate::leanh::lean_dec_ref(v_unusedParams_5358_);
                v___x_5379_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5380_ = lean_nat_dec_eq(v___x_5378_, v___x_5379_);
                if v___x_5380_ == 0 {
                    v___x_5381_ = l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__4;
                    v___y_5372_ = v___x_5381_;
                    state = 1;
                    continue;
                } else {
                    v___x_5382_ = l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__5;
                    v___y_5372_ = v___x_5382_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_5372_);
                v___x_5373_ = l_Lean_stringToMessageData(v___y_5372_);
                v___x_5374_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5374_, 0, v___x_5370_);
                crate::leanh::lean_ctor_set(v___x_5374_, 1, v___x_5373_);
                v___x_5375_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__3), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__3_once), _init_l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___closed__3);
                v___x_5376_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5376_, 0, v___x_5374_);
                crate::leanh::lean_ctor_set(v___x_5376_, 1, v___x_5375_);
                v___x_5377_ = l_Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3(v___x_5357_, v_ref_5366_, v___x_5376_, v___y_5359_, v___y_5360_, v___y_5361_, v___y_5362_, v___y_5363_, v___y_5364_);
                return v___x_5377_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___boxed(
    mut v_head_5383_: *mut crate::leanh::LeanObject,
    mut v___x_5384_: *mut crate::leanh::LeanObject,
    mut v_unusedParams_5385_: *mut crate::leanh::LeanObject,
    mut v___y_5386_: *mut crate::leanh::LeanObject,
    mut v___y_5387_: *mut crate::leanh::LeanObject,
    mut v___y_5388_: *mut crate::leanh::LeanObject,
    mut v___y_5389_: *mut crate::leanh::LeanObject,
    mut v___y_5390_: *mut crate::leanh::LeanObject,
    mut v___y_5391_: *mut crate::leanh::LeanObject,
    mut v___y_5392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5393_ = l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0(v_head_5383_, v___x_5384_, v_unusedParams_5385_, v___y_5386_, v___y_5387_, v___y_5388_, v___y_5389_, v___y_5390_, v___y_5391_);
    crate::leanh::lean_dec(v___y_5391_);
    crate::leanh::lean_dec_ref(v___y_5390_);
    crate::leanh::lean_dec(v___y_5389_);
    crate::leanh::lean_dec_ref(v___y_5388_);
    crate::leanh::lean_dec(v___y_5387_);
    crate::leanh::lean_dec_ref(v___y_5386_);
    return v_res_5393_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg(
    mut v_as_x27_5394_: *mut crate::leanh::LeanObject,
    mut v_b_5395_: *mut crate::leanh::LeanObject,
    mut v___y_5396_: *mut crate::leanh::LeanObject,
    mut v___y_5397_: *mut crate::leanh::LeanObject,
    mut v___y_5398_: *mut crate::leanh::LeanObject,
    mut v___y_5399_: *mut crate::leanh::LeanObject,
    mut v___y_5400_: *mut crate::leanh::LeanObject,
    mut v___y_5401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_5394_) == 0 {
                    v___x_5403_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5403_, 0, v_b_5395_);
                    return v___x_5403_;
                } else {
                    v_head_5404_ = crate::leanh::lean_ctor_get(v_as_x27_5394_, 0);
                    v_tail_5405_ = crate::leanh::lean_ctor_get(v_as_x27_5394_, 1);
                    v___x_5406_ = l_Lean_Linter_Extra_linter_extra_unusedDecidableInType;
                    crate::leanh::lean_inc_n(v_head_5404_, 2);
                    v___f_5407_ = crate::leanh::lean_alloc_closure(l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 2);
                    crate::leanh::lean_closure_set(v___f_5407_, 0, v_head_5404_);
                    crate::leanh::lean_closure_set(v___f_5407_, 1, v___x_5406_);
                    v___x_5408_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2___closed__0;
                    v___x_5409_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_onUnusedInstancesWhere(v_head_5404_, v___x_5408_, v___f_5407_, v___y_5396_, v___y_5397_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_);
                    if crate::leanh::lean_obj_tag(v___x_5409_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5409_, 1);
                        v___x_5410_ = crate::leanh::lean_box(0);
                        v_as_x27_5394_ = v_tail_5405_;
                        v_b_5395_ = v___x_5410_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5409_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg___boxed(
    mut v_as_x27_5412_: *mut crate::leanh::LeanObject,
    mut v_b_5413_: *mut crate::leanh::LeanObject,
    mut v___y_5414_: *mut crate::leanh::LeanObject,
    mut v___y_5415_: *mut crate::leanh::LeanObject,
    mut v___y_5416_: *mut crate::leanh::LeanObject,
    mut v___y_5417_: *mut crate::leanh::LeanObject,
    mut v___y_5418_: *mut crate::leanh::LeanObject,
    mut v___y_5419_: *mut crate::leanh::LeanObject,
    mut v___y_5420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5421_ = l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg(v_as_x27_5412_, v_b_5413_, v___y_5414_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_, v___y_5419_);
    crate::leanh::lean_dec(v___y_5419_);
    crate::leanh::lean_dec_ref(v___y_5418_);
    crate::leanh::lean_dec(v___y_5417_);
    crate::leanh::lean_dec_ref(v___y_5416_);
    crate::leanh::lean_dec(v___y_5415_);
    crate::leanh::lean_dec_ref(v___y_5414_);
    crate::leanh::lean_dec(v_as_x27_5412_);
    return v_res_5421_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0(
    mut v___x_5422_: *mut crate::leanh::LeanObject,
    mut v___x_5423_: *mut crate::leanh::LeanObject,
    mut v___y_5424_: *mut crate::leanh::LeanObject,
    mut v___y_5425_: *mut crate::leanh::LeanObject,
    mut v___y_5426_: *mut crate::leanh::LeanObject,
    mut v___y_5427_: *mut crate::leanh::LeanObject,
    mut v___y_5428_: *mut crate::leanh::LeanObject,
    mut v___y_5429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5434_: u8 = 0;
    let mut v___x_5436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5438_: u8 = 0;
    let mut v_unused_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5431_ = l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg(v___x_5422_, v___x_5423_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_);
                if crate::leanh::lean_obj_tag(v___x_5431_) == 0 {
                    v_isSharedCheck_5438_ = (!crate::leanh::lean_is_exclusive(v___x_5431_)) as u8;
                    if v_isSharedCheck_5438_ == 0 {
                        v_unused_5439_ = crate::leanh::lean_ctor_get(v___x_5431_, 0);
                        crate::leanh::lean_dec(v_unused_5439_);
                        v___x_5433_ = v___x_5431_;
                        v_isShared_5434_ = v_isSharedCheck_5438_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5431_);
                        v___x_5433_ = crate::leanh::lean_box(0);
                        v_isShared_5434_ = v_isSharedCheck_5438_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_5431_;
                }
            }
            1 => {
                if v_isShared_5434_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5433_, 0, v___x_5423_);
                    v___x_5436_ = v___x_5433_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5437_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5437_, 0, v___x_5423_);
                    v___x_5436_ = v_reuseFailAlloc_5437_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5436_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0___boxed(
    mut v___x_5440_: *mut crate::leanh::LeanObject,
    mut v___x_5441_: *mut crate::leanh::LeanObject,
    mut v___y_5442_: *mut crate::leanh::LeanObject,
    mut v___y_5443_: *mut crate::leanh::LeanObject,
    mut v___y_5444_: *mut crate::leanh::LeanObject,
    mut v___y_5445_: *mut crate::leanh::LeanObject,
    mut v___y_5446_: *mut crate::leanh::LeanObject,
    mut v___y_5447_: *mut crate::leanh::LeanObject,
    mut v___y_5448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0(v___x_5440_, v___x_5441_, v___y_5442_, v___y_5443_, v___y_5444_, v___y_5445_, v___y_5446_, v___y_5447_);
    crate::leanh::lean_dec(v___y_5447_);
    crate::leanh::lean_dec_ref(v___y_5446_);
    crate::leanh::lean_dec(v___y_5445_);
    crate::leanh::lean_dec_ref(v___y_5444_);
    crate::leanh::lean_dec(v___y_5443_);
    crate::leanh::lean_dec_ref(v___y_5442_);
    crate::leanh::lean_dec(v___x_5440_);
    return v_res_5449_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12_spec__14(
    mut v___x_5450_: *mut crate::leanh::LeanObject,
    mut v___x_5451_: u8,
    mut v_as_5452_: *mut crate::leanh::LeanObject,
    mut v_sz_5453_: usize,
    mut v_i_5454_: usize,
    mut v_b_5455_: *mut crate::leanh::LeanObject,
    mut v___y_5456_: *mut crate::leanh::LeanObject,
    mut v___y_5457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5459_: u8 = 0;
    let mut v___x_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: usize = 0;
    let mut v___x_5466_: usize = 0;
    let mut v___x_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: u8 = 0;
    let mut v___f_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5479_: u8 = 0;
    let mut v___x_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5483_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5459_ = lean_usize_dec_lt(v_i_5454_, v_sz_5453_);
                if v___x_5459_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_5450_);
                    v___x_5460_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5460_, 0, v_b_5455_);
                    return v___x_5460_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_5455_);
                    v___x_5461_ = crate::leanh::lean_box(0);
                    v___x_5468_ = crate::leanh::lean_box(0);
                    v_a_5469_ = lean_array_uget_borrowed(v_as_5452_, v_i_5454_);
                    crate::leanh::lean_inc_ref(v___x_5450_);
                    crate::leanh::lean_inc(v_a_5469_);
                    v___x_5470_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems(v_a_5469_, v___x_5450_);
                    v___x_5471_ = crate::leanh::lean_box(0);
                    v___x_5472_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2(v___x_5451_, v___x_5470_, v___x_5471_);
                    v___x_5473_ = l_List_isEmpty___redArg(v___x_5472_);
                    if v___x_5473_ == 0 {
                        v___f_5474_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0___boxed as *mut core::ffi::c_void, 9, 2);
                        crate::leanh::lean_closure_set(v___f_5474_, 0, v___x_5472_);
                        crate::leanh::lean_closure_set(v___f_5474_, 1, v___x_5468_);
                        v___x_5475_ = l_Lean_Elab_Command_liftTermElabM___redArg(
                            v___f_5474_,
                            v___y_5456_,
                            v___y_5457_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5475_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5475_, 1);
                            v_a_5463_ = v___x_5468_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___x_5450_);
                            v_a_5476_ = crate::leanh::lean_ctor_get(v___x_5475_, 0);
                            v_isSharedCheck_5483_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5475_)) as u8;
                            if v_isSharedCheck_5483_ == 0 {
                                v___x_5478_ = v___x_5475_;
                                v_isShared_5479_ = v_isSharedCheck_5483_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5476_);
                                crate::leanh::lean_dec(v___x_5475_);
                                v___x_5478_ = crate::leanh::lean_box(0);
                                v_isShared_5479_ = v_isSharedCheck_5483_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5472_);
                        v_a_5463_ = v___x_5468_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5464_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5464_, 0, v___x_5461_);
                crate::leanh::lean_ctor_set(v___x_5464_, 1, v_a_5463_);
                v___x_5465_ = 1usize;
                v___x_5466_ = lean_usize_add(v_i_5454_, v___x_5465_);
                v_i_5454_ = v___x_5466_;
                v_b_5455_ = v___x_5464_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_5479_ == 0 {
                    v___x_5481_ = v___x_5478_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5482_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5482_, 0, v_a_5476_);
                    v___x_5481_ = v_reuseFailAlloc_5482_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5481_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12_spec__14___boxed(
    mut v___x_5484_: *mut crate::leanh::LeanObject,
    mut v___x_5485_: *mut crate::leanh::LeanObject,
    mut v_as_5486_: *mut crate::leanh::LeanObject,
    mut v_sz_5487_: *mut crate::leanh::LeanObject,
    mut v_i_5488_: *mut crate::leanh::LeanObject,
    mut v_b_5489_: *mut crate::leanh::LeanObject,
    mut v___y_5490_: *mut crate::leanh::LeanObject,
    mut v___y_5491_: *mut crate::leanh::LeanObject,
    mut v___y_5492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_13257__boxed_5493_: u8 = 0;
    let mut v_sz_boxed_5494_: usize = 0;
    let mut v_i_boxed_5495_: usize = 0;
    let mut v_res_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_13257__boxed_5493_ = (crate::leanh::lean_unbox(v___x_5485_) as u8);
    v_sz_boxed_5494_ = crate::leanh::lean_unbox_usize(v_sz_5487_);
    crate::leanh::lean_dec(v_sz_5487_);
    v_i_boxed_5495_ = crate::leanh::lean_unbox_usize(v_i_5488_);
    crate::leanh::lean_dec(v_i_5488_);
    v_res_5496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12_spec__14(v___x_5484_, v___x_13257__boxed_5493_, v_as_5486_, v_sz_boxed_5494_, v_i_boxed_5495_, v_b_5489_, v___y_5490_, v___y_5491_);
    crate::leanh::lean_dec(v___y_5491_);
    crate::leanh::lean_dec_ref(v___y_5490_);
    crate::leanh::lean_dec_ref(v_as_5486_);
    return v_res_5496_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12(
    mut v___x_5500_: *mut crate::leanh::LeanObject,
    mut v___x_5501_: u8,
    mut v_as_5502_: *mut crate::leanh::LeanObject,
    mut v_sz_5503_: usize,
    mut v_i_5504_: usize,
    mut v_b_5505_: *mut crate::leanh::LeanObject,
    mut v___y_5506_: *mut crate::leanh::LeanObject,
    mut v___y_5507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5509_: u8 = 0;
    let mut v___x_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: usize = 0;
    let mut v___x_5515_: usize = 0;
    let mut v___x_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: u8 = 0;
    let mut v___f_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5527_: u8 = 0;
    let mut v___x_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5531_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5509_ = lean_usize_dec_lt(v_i_5504_, v_sz_5503_);
                if v___x_5509_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_5500_);
                    v___x_5510_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5510_, 0, v_b_5505_);
                    return v___x_5510_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_5505_);
                    v___x_5511_ = crate::leanh::lean_box(0);
                    v_a_5517_ = lean_array_uget_borrowed(v_as_5502_, v_i_5504_);
                    crate::leanh::lean_inc_ref(v___x_5500_);
                    crate::leanh::lean_inc(v_a_5517_);
                    v___x_5518_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems(v_a_5517_, v___x_5500_);
                    v___x_5519_ = crate::leanh::lean_box(0);
                    v___x_5520_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2(v___x_5501_, v___x_5518_, v___x_5519_);
                    v___x_5521_ = l_List_isEmpty___redArg(v___x_5520_);
                    if v___x_5521_ == 0 {
                        v___f_5522_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0___boxed as *mut core::ffi::c_void, 9, 2);
                        crate::leanh::lean_closure_set(v___f_5522_, 0, v___x_5520_);
                        crate::leanh::lean_closure_set(v___f_5522_, 1, v___x_5511_);
                        v___x_5523_ = l_Lean_Elab_Command_liftTermElabM___redArg(
                            v___f_5522_,
                            v___y_5506_,
                            v___y_5507_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5523_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5523_, 1);
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___x_5500_);
                            v_a_5524_ = crate::leanh::lean_ctor_get(v___x_5523_, 0);
                            v_isSharedCheck_5531_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5523_)) as u8;
                            if v_isSharedCheck_5531_ == 0 {
                                v___x_5526_ = v___x_5523_;
                                v_isShared_5527_ = v_isSharedCheck_5531_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5524_);
                                crate::leanh::lean_dec(v___x_5523_);
                                v___x_5526_ = crate::leanh::lean_box(0);
                                v_isShared_5527_ = v_isSharedCheck_5531_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5520_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5513_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12___closed__0;
                v___x_5514_ = 1usize;
                v___x_5515_ = lean_usize_add(v_i_5504_, v___x_5514_);
                v___x_5516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12_spec__14(v___x_5500_, v___x_5501_, v_as_5502_, v_sz_5503_, v___x_5515_, v___x_5513_, v___y_5506_, v___y_5507_);
                return v___x_5516_;
            }
            2 => {
                if v_isShared_5527_ == 0 {
                    v___x_5529_ = v___x_5526_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5530_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5530_, 0, v_a_5524_);
                    v___x_5529_ = v_reuseFailAlloc_5530_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5529_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12___boxed(
    mut v___x_5532_: *mut crate::leanh::LeanObject,
    mut v___x_5533_: *mut crate::leanh::LeanObject,
    mut v_as_5534_: *mut crate::leanh::LeanObject,
    mut v_sz_5535_: *mut crate::leanh::LeanObject,
    mut v_i_5536_: *mut crate::leanh::LeanObject,
    mut v_b_5537_: *mut crate::leanh::LeanObject,
    mut v___y_5538_: *mut crate::leanh::LeanObject,
    mut v___y_5539_: *mut crate::leanh::LeanObject,
    mut v___y_5540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_13327__boxed_5541_: u8 = 0;
    let mut v_sz_boxed_5542_: usize = 0;
    let mut v_i_boxed_5543_: usize = 0;
    let mut v_res_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_13327__boxed_5541_ = (crate::leanh::lean_unbox(v___x_5533_) as u8);
    v_sz_boxed_5542_ = crate::leanh::lean_unbox_usize(v_sz_5535_);
    crate::leanh::lean_dec(v_sz_5535_);
    v_i_boxed_5543_ = crate::leanh::lean_unbox_usize(v_i_5536_);
    crate::leanh::lean_dec(v_i_5536_);
    v_res_5544_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12(v___x_5532_, v___x_13327__boxed_5541_, v_as_5534_, v_sz_boxed_5542_, v_i_boxed_5543_, v_b_5537_, v___y_5538_, v___y_5539_);
    crate::leanh::lean_dec(v___y_5539_);
    crate::leanh::lean_dec_ref(v___y_5538_);
    crate::leanh::lean_dec_ref(v_as_5534_);
    return v_res_5544_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8(
    mut v_init_5545_: *mut crate::leanh::LeanObject,
    mut v___x_5546_: *mut crate::leanh::LeanObject,
    mut v___x_5547_: u8,
    mut v_n_5548_: *mut crate::leanh::LeanObject,
    mut v_b_5549_: *mut crate::leanh::LeanObject,
    mut v___y_5550_: *mut crate::leanh::LeanObject,
    mut v___y_5551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5556_: usize = 0;
    let mut v___x_5557_: usize = 0;
    let mut v___x_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5562_: u8 = 0;
    let mut v_fst_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5573_: u8 = 0;
    let mut v_a_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5577_: u8 = 0;
    let mut v___x_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5581_: u8 = 0;
    let mut v_vs_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5585_: usize = 0;
    let mut v___x_5586_: usize = 0;
    let mut v___x_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5591_: u8 = 0;
    let mut v_fst_5592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5602_: u8 = 0;
    let mut v_a_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5606_: u8 = 0;
    let mut v___x_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5610_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_5548_) == 0 {
                    v_cs_5553_ = crate::leanh::lean_ctor_get(v_n_5548_, 0);
                    v___x_5554_ = crate::leanh::lean_box(0);
                    v___x_5555_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5555_, 0, v___x_5554_);
                    crate::leanh::lean_ctor_set(v___x_5555_, 1, v_b_5549_);
                    v_sz_5556_ = lean_array_size(v_cs_5553_);
                    v___x_5557_ = 0usize;
                    v___x_5558_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__11(v_init_5545_, v___x_5546_, v___x_5547_, v_cs_5553_, v_sz_5556_, v___x_5557_, v___x_5555_, v___y_5550_, v___y_5551_);
                    if crate::leanh::lean_obj_tag(v___x_5558_) == 0 {
                        v_a_5559_ = crate::leanh::lean_ctor_get(v___x_5558_, 0);
                        v_isSharedCheck_5573_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5558_)) as u8;
                        if v_isSharedCheck_5573_ == 0 {
                            v___x_5561_ = v___x_5558_;
                            v_isShared_5562_ = v_isSharedCheck_5573_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5559_);
                            crate::leanh::lean_dec(v___x_5558_);
                            v___x_5561_ = crate::leanh::lean_box(0);
                            v_isShared_5562_ = v_isSharedCheck_5573_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5574_ = crate::leanh::lean_ctor_get(v___x_5558_, 0);
                        v_isSharedCheck_5581_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5558_)) as u8;
                        if v_isSharedCheck_5581_ == 0 {
                            v___x_5576_ = v___x_5558_;
                            v_isShared_5577_ = v_isSharedCheck_5581_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5574_);
                            crate::leanh::lean_dec(v___x_5558_);
                            v___x_5576_ = crate::leanh::lean_box(0);
                            v_isShared_5577_ = v_isSharedCheck_5581_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_5582_ = crate::leanh::lean_ctor_get(v_n_5548_, 0);
                    v___x_5583_ = crate::leanh::lean_box(0);
                    v___x_5584_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5584_, 0, v___x_5583_);
                    crate::leanh::lean_ctor_set(v___x_5584_, 1, v_b_5549_);
                    v_sz_5585_ = lean_array_size(v_vs_5582_);
                    v___x_5586_ = 0usize;
                    v___x_5587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__12(v___x_5546_, v___x_5547_, v_vs_5582_, v_sz_5585_, v___x_5586_, v___x_5584_, v___y_5550_, v___y_5551_);
                    if crate::leanh::lean_obj_tag(v___x_5587_) == 0 {
                        v_a_5588_ = crate::leanh::lean_ctor_get(v___x_5587_, 0);
                        v_isSharedCheck_5602_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5587_)) as u8;
                        if v_isSharedCheck_5602_ == 0 {
                            v___x_5590_ = v___x_5587_;
                            v_isShared_5591_ = v_isSharedCheck_5602_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5588_);
                            crate::leanh::lean_dec(v___x_5587_);
                            v___x_5590_ = crate::leanh::lean_box(0);
                            v_isShared_5591_ = v_isSharedCheck_5602_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_5603_ = crate::leanh::lean_ctor_get(v___x_5587_, 0);
                        v_isSharedCheck_5610_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5587_)) as u8;
                        if v_isSharedCheck_5610_ == 0 {
                            v___x_5605_ = v___x_5587_;
                            v_isShared_5606_ = v_isSharedCheck_5610_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5603_);
                            crate::leanh::lean_dec(v___x_5587_);
                            v___x_5605_ = crate::leanh::lean_box(0);
                            v_isShared_5606_ = v_isSharedCheck_5610_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_5563_ = crate::leanh::lean_ctor_get(v_a_5559_, 0);
                if crate::leanh::lean_obj_tag(v_fst_5563_) == 0 {
                    v_snd_5564_ = crate::leanh::lean_ctor_get(v_a_5559_, 1);
                    crate::leanh::lean_inc(v_snd_5564_);
                    crate::leanh::lean_dec(v_a_5559_);
                    v___x_5565_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5565_, 0, v_snd_5564_);
                    if v_isShared_5562_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5561_, 0, v___x_5565_);
                        v___x_5567_ = v___x_5561_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5568_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5568_, 0, v___x_5565_);
                        v___x_5567_ = v_reuseFailAlloc_5568_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_5563_);
                    crate::leanh::lean_dec(v_a_5559_);
                    v_val_5569_ = crate::leanh::lean_ctor_get(v_fst_5563_, 0);
                    crate::leanh::lean_inc(v_val_5569_);
                    crate::leanh::lean_dec_ref_known(v_fst_5563_, 1);
                    if v_isShared_5562_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5561_, 0, v_val_5569_);
                        v___x_5571_ = v___x_5561_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5572_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5572_, 0, v_val_5569_);
                        v___x_5571_ = v_reuseFailAlloc_5572_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5567_;
            }
            3 => {
                return v___x_5571_;
            }
            4 => {
                if v_isShared_5577_ == 0 {
                    v___x_5579_ = v___x_5576_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5580_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5580_, 0, v_a_5574_);
                    v___x_5579_ = v_reuseFailAlloc_5580_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5579_;
            }
            6 => {
                v_fst_5592_ = crate::leanh::lean_ctor_get(v_a_5588_, 0);
                if crate::leanh::lean_obj_tag(v_fst_5592_) == 0 {
                    v_snd_5593_ = crate::leanh::lean_ctor_get(v_a_5588_, 1);
                    crate::leanh::lean_inc(v_snd_5593_);
                    crate::leanh::lean_dec(v_a_5588_);
                    v___x_5594_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5594_, 0, v_snd_5593_);
                    if v_isShared_5591_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5590_, 0, v___x_5594_);
                        v___x_5596_ = v___x_5590_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5597_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5597_, 0, v___x_5594_);
                        v___x_5596_ = v_reuseFailAlloc_5597_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_5592_);
                    crate::leanh::lean_dec(v_a_5588_);
                    v_val_5598_ = crate::leanh::lean_ctor_get(v_fst_5592_, 0);
                    crate::leanh::lean_inc(v_val_5598_);
                    crate::leanh::lean_dec_ref_known(v_fst_5592_, 1);
                    if v_isShared_5591_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5590_, 0, v_val_5598_);
                        v___x_5600_ = v___x_5590_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5601_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5601_, 0, v_val_5598_);
                        v___x_5600_ = v_reuseFailAlloc_5601_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_5596_;
            }
            8 => {
                return v___x_5600_;
            }
            9 => {
                if v_isShared_5606_ == 0 {
                    v___x_5608_ = v___x_5605_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5609_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5609_, 0, v_a_5603_);
                    v___x_5608_ = v_reuseFailAlloc_5609_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5608_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__11(
    mut v_init_5611_: *mut crate::leanh::LeanObject,
    mut v___x_5612_: *mut crate::leanh::LeanObject,
    mut v___x_5613_: u8,
    mut v_as_5614_: *mut crate::leanh::LeanObject,
    mut v_sz_5615_: usize,
    mut v_i_5616_: usize,
    mut v_b_5617_: *mut crate::leanh::LeanObject,
    mut v___y_5618_: *mut crate::leanh::LeanObject,
    mut v___y_5619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5621_: u8 = 0;
    let mut v___x_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5626_: u8 = 0;
    let mut v_a_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5632_: u8 = 0;
    let mut v___x_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: usize = 0;
    let mut v___x_5645_: usize = 0;
    let mut v_reuseFailAlloc_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5648_: u8 = 0;
    let mut v_a_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5652_: u8 = 0;
    let mut v___x_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5656_: u8 = 0;
    let mut v_isSharedCheck_5657_: u8 = 0;
    let mut v_unused_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5621_ = lean_usize_dec_lt(v_i_5616_, v_sz_5615_);
                if v___x_5621_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_5612_);
                    v___x_5622_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5622_, 0, v_b_5617_);
                    return v___x_5622_;
                } else {
                    v_snd_5623_ = crate::leanh::lean_ctor_get(v_b_5617_, 1);
                    v_isSharedCheck_5657_ = (!crate::leanh::lean_is_exclusive(v_b_5617_)) as u8;
                    if v_isSharedCheck_5657_ == 0 {
                        v_unused_5658_ = crate::leanh::lean_ctor_get(v_b_5617_, 0);
                        crate::leanh::lean_dec(v_unused_5658_);
                        v___x_5625_ = v_b_5617_;
                        v_isShared_5626_ = v_isSharedCheck_5657_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5623_);
                        crate::leanh::lean_dec(v_b_5617_);
                        v___x_5625_ = crate::leanh::lean_box(0);
                        v_isShared_5626_ = v_isSharedCheck_5657_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5627_ = lean_array_uget_borrowed(v_as_5614_, v_i_5616_);
                crate::leanh::lean_inc(v_snd_5623_);
                crate::leanh::lean_inc_ref(v___x_5612_);
                v___x_5628_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8(v_init_5611_, v___x_5612_, v___x_5613_, v_a_5627_, v_snd_5623_, v___y_5618_, v___y_5619_);
                if crate::leanh::lean_obj_tag(v___x_5628_) == 0 {
                    v_a_5629_ = crate::leanh::lean_ctor_get(v___x_5628_, 0);
                    v_isSharedCheck_5648_ = (!crate::leanh::lean_is_exclusive(v___x_5628_)) as u8;
                    if v_isSharedCheck_5648_ == 0 {
                        v___x_5631_ = v___x_5628_;
                        v_isShared_5632_ = v_isSharedCheck_5648_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5629_);
                        crate::leanh::lean_dec(v___x_5628_);
                        v___x_5631_ = crate::leanh::lean_box(0);
                        v_isShared_5632_ = v_isSharedCheck_5648_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5625_);
                    crate::leanh::lean_dec(v_snd_5623_);
                    crate::leanh::lean_dec_ref(v___x_5612_);
                    v_a_5649_ = crate::leanh::lean_ctor_get(v___x_5628_, 0);
                    v_isSharedCheck_5656_ = (!crate::leanh::lean_is_exclusive(v___x_5628_)) as u8;
                    if v_isSharedCheck_5656_ == 0 {
                        v___x_5651_ = v___x_5628_;
                        v_isShared_5652_ = v_isSharedCheck_5656_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5649_);
                        crate::leanh::lean_dec(v___x_5628_);
                        v___x_5651_ = crate::leanh::lean_box(0);
                        v_isShared_5652_ = v_isSharedCheck_5656_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_5629_) == 0 {
                    crate::leanh::lean_dec_ref(v___x_5612_);
                    v___x_5633_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5633_, 0, v_a_5629_);
                    if v_isShared_5626_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5625_, 0, v___x_5633_);
                        v___x_5635_ = v___x_5625_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5639_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5639_, 0, v___x_5633_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5639_, 1, v_snd_5623_);
                        v___x_5635_ = v_reuseFailAlloc_5639_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5631_);
                    crate::leanh::lean_dec(v_snd_5623_);
                    v_a_5640_ = crate::leanh::lean_ctor_get(v_a_5629_, 0);
                    crate::leanh::lean_inc(v_a_5640_);
                    crate::leanh::lean_dec_ref_known(v_a_5629_, 1);
                    v___x_5641_ = crate::leanh::lean_box(0);
                    if v_isShared_5626_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5625_, 1, v_a_5640_);
                        crate::leanh::lean_ctor_set(v___x_5625_, 0, v___x_5641_);
                        v___x_5643_ = v___x_5625_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5647_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5647_, 0, v___x_5641_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5647_, 1, v_a_5640_);
                        v___x_5643_ = v_reuseFailAlloc_5647_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5632_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5631_, 0, v___x_5635_);
                    v___x_5637_ = v___x_5631_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5638_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5638_, 0, v___x_5635_);
                    v___x_5637_ = v_reuseFailAlloc_5638_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5637_;
            }
            5 => {
                v___x_5644_ = 1usize;
                v___x_5645_ = lean_usize_add(v_i_5616_, v___x_5644_);
                v_i_5616_ = v___x_5645_;
                v_b_5617_ = v___x_5643_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_5652_ == 0 {
                    v___x_5654_ = v___x_5651_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5655_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5655_, 0, v_a_5649_);
                    v___x_5654_ = v_reuseFailAlloc_5655_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5654_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__11___boxed(
    mut v_init_5659_: *mut crate::leanh::LeanObject,
    mut v___x_5660_: *mut crate::leanh::LeanObject,
    mut v___x_5661_: *mut crate::leanh::LeanObject,
    mut v_as_5662_: *mut crate::leanh::LeanObject,
    mut v_sz_5663_: *mut crate::leanh::LeanObject,
    mut v_i_5664_: *mut crate::leanh::LeanObject,
    mut v_b_5665_: *mut crate::leanh::LeanObject,
    mut v___y_5666_: *mut crate::leanh::LeanObject,
    mut v___y_5667_: *mut crate::leanh::LeanObject,
    mut v___y_5668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_13390__boxed_5669_: u8 = 0;
    let mut v_sz_boxed_5670_: usize = 0;
    let mut v_i_boxed_5671_: usize = 0;
    let mut v_res_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_13390__boxed_5669_ = (crate::leanh::lean_unbox(v___x_5661_) as u8);
    v_sz_boxed_5670_ = crate::leanh::lean_unbox_usize(v_sz_5663_);
    crate::leanh::lean_dec(v_sz_5663_);
    v_i_boxed_5671_ = crate::leanh::lean_unbox_usize(v_i_5664_);
    crate::leanh::lean_dec(v_i_5664_);
    v_res_5672_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8_spec__11(v_init_5659_, v___x_5660_, v___x_13390__boxed_5669_, v_as_5662_, v_sz_boxed_5670_, v_i_boxed_5671_, v_b_5665_, v___y_5666_, v___y_5667_);
    crate::leanh::lean_dec(v___y_5667_);
    crate::leanh::lean_dec_ref(v___y_5666_);
    crate::leanh::lean_dec_ref(v_as_5662_);
    return v_res_5672_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8___boxed(
    mut v_init_5673_: *mut crate::leanh::LeanObject,
    mut v___x_5674_: *mut crate::leanh::LeanObject,
    mut v___x_5675_: *mut crate::leanh::LeanObject,
    mut v_n_5676_: *mut crate::leanh::LeanObject,
    mut v_b_5677_: *mut crate::leanh::LeanObject,
    mut v___y_5678_: *mut crate::leanh::LeanObject,
    mut v___y_5679_: *mut crate::leanh::LeanObject,
    mut v___y_5680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_13411__boxed_5681_: u8 = 0;
    let mut v_res_5682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_13411__boxed_5681_ = (crate::leanh::lean_unbox(v___x_5675_) as u8);
    v_res_5682_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8(v_init_5673_, v___x_5674_, v___x_13411__boxed_5681_, v_n_5676_, v_b_5677_, v___y_5678_, v___y_5679_);
    crate::leanh::lean_dec(v___y_5679_);
    crate::leanh::lean_dec_ref(v___y_5678_);
    crate::leanh::lean_dec_ref(v_n_5676_);
    return v_res_5682_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9_spec__14(
    mut v___x_5683_: *mut crate::leanh::LeanObject,
    mut v___x_5684_: u8,
    mut v_as_5685_: *mut crate::leanh::LeanObject,
    mut v_sz_5686_: usize,
    mut v_i_5687_: usize,
    mut v_b_5688_: *mut crate::leanh::LeanObject,
    mut v___y_5689_: *mut crate::leanh::LeanObject,
    mut v___y_5690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5692_: u8 = 0;
    let mut v___x_5693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: usize = 0;
    let mut v___x_5699_: usize = 0;
    let mut v___x_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: u8 = 0;
    let mut v___f_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5712_: u8 = 0;
    let mut v___x_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5716_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5692_ = lean_usize_dec_lt(v_i_5687_, v_sz_5686_);
                if v___x_5692_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_5683_);
                    v___x_5693_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5693_, 0, v_b_5688_);
                    return v___x_5693_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_5688_);
                    v___x_5694_ = crate::leanh::lean_box(0);
                    v___x_5701_ = crate::leanh::lean_box(0);
                    v_a_5702_ = lean_array_uget_borrowed(v_as_5685_, v_i_5687_);
                    crate::leanh::lean_inc_ref(v___x_5683_);
                    crate::leanh::lean_inc(v_a_5702_);
                    v___x_5703_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems(v_a_5702_, v___x_5683_);
                    v___x_5704_ = crate::leanh::lean_box(0);
                    v___x_5705_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2(v___x_5684_, v___x_5703_, v___x_5704_);
                    v___x_5706_ = l_List_isEmpty___redArg(v___x_5705_);
                    if v___x_5706_ == 0 {
                        v___f_5707_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0___boxed as *mut core::ffi::c_void, 9, 2);
                        crate::leanh::lean_closure_set(v___f_5707_, 0, v___x_5705_);
                        crate::leanh::lean_closure_set(v___f_5707_, 1, v___x_5701_);
                        v___x_5708_ = l_Lean_Elab_Command_liftTermElabM___redArg(
                            v___f_5707_,
                            v___y_5689_,
                            v___y_5690_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5708_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5708_, 1);
                            v_a_5696_ = v___x_5701_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___x_5683_);
                            v_a_5709_ = crate::leanh::lean_ctor_get(v___x_5708_, 0);
                            v_isSharedCheck_5716_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5708_)) as u8;
                            if v_isSharedCheck_5716_ == 0 {
                                v___x_5711_ = v___x_5708_;
                                v_isShared_5712_ = v_isSharedCheck_5716_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5709_);
                                crate::leanh::lean_dec(v___x_5708_);
                                v___x_5711_ = crate::leanh::lean_box(0);
                                v_isShared_5712_ = v_isSharedCheck_5716_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5705_);
                        v_a_5696_ = v___x_5701_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5697_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5697_, 0, v___x_5694_);
                crate::leanh::lean_ctor_set(v___x_5697_, 1, v_a_5696_);
                v___x_5698_ = 1usize;
                v___x_5699_ = lean_usize_add(v_i_5687_, v___x_5698_);
                v_i_5687_ = v___x_5699_;
                v_b_5688_ = v___x_5697_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_5712_ == 0 {
                    v___x_5714_ = v___x_5711_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5715_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5715_, 0, v_a_5709_);
                    v___x_5714_ = v_reuseFailAlloc_5715_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5714_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9_spec__14___boxed(
    mut v___x_5717_: *mut crate::leanh::LeanObject,
    mut v___x_5718_: *mut crate::leanh::LeanObject,
    mut v_as_5719_: *mut crate::leanh::LeanObject,
    mut v_sz_5720_: *mut crate::leanh::LeanObject,
    mut v_i_5721_: *mut crate::leanh::LeanObject,
    mut v_b_5722_: *mut crate::leanh::LeanObject,
    mut v___y_5723_: *mut crate::leanh::LeanObject,
    mut v___y_5724_: *mut crate::leanh::LeanObject,
    mut v___y_5725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_13597__boxed_5726_: u8 = 0;
    let mut v_sz_boxed_5727_: usize = 0;
    let mut v_i_boxed_5728_: usize = 0;
    let mut v_res_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_13597__boxed_5726_ = (crate::leanh::lean_unbox(v___x_5718_) as u8);
    v_sz_boxed_5727_ = crate::leanh::lean_unbox_usize(v_sz_5720_);
    crate::leanh::lean_dec(v_sz_5720_);
    v_i_boxed_5728_ = crate::leanh::lean_unbox_usize(v_i_5721_);
    crate::leanh::lean_dec(v_i_5721_);
    v_res_5729_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9_spec__14(v___x_5717_, v___x_13597__boxed_5726_, v_as_5719_, v_sz_boxed_5727_, v_i_boxed_5728_, v_b_5722_, v___y_5723_, v___y_5724_);
    crate::leanh::lean_dec(v___y_5724_);
    crate::leanh::lean_dec_ref(v___y_5723_);
    crate::leanh::lean_dec_ref(v_as_5719_);
    return v_res_5729_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9(
    mut v___x_5733_: *mut crate::leanh::LeanObject,
    mut v___x_5734_: u8,
    mut v_as_5735_: *mut crate::leanh::LeanObject,
    mut v_sz_5736_: usize,
    mut v_i_5737_: usize,
    mut v_b_5738_: *mut crate::leanh::LeanObject,
    mut v___y_5739_: *mut crate::leanh::LeanObject,
    mut v___y_5740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5742_: u8 = 0;
    let mut v___x_5743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: usize = 0;
    let mut v___x_5748_: usize = 0;
    let mut v___x_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: u8 = 0;
    let mut v___f_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5760_: u8 = 0;
    let mut v___x_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5764_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5742_ = lean_usize_dec_lt(v_i_5737_, v_sz_5736_);
                if v___x_5742_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_5733_);
                    v___x_5743_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5743_, 0, v_b_5738_);
                    return v___x_5743_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_5738_);
                    v___x_5744_ = crate::leanh::lean_box(0);
                    v_a_5750_ = lean_array_uget_borrowed(v_as_5735_, v_i_5737_);
                    crate::leanh::lean_inc_ref(v___x_5733_);
                    crate::leanh::lean_inc(v_a_5750_);
                    v___x_5751_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_getTheorems(v_a_5750_, v___x_5733_);
                    v___x_5752_ = crate::leanh::lean_box(0);
                    v___x_5753_ = l_List_filterTR_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__2(v___x_5734_, v___x_5751_, v___x_5752_);
                    v___x_5754_ = l_List_isEmpty___redArg(v___x_5753_);
                    if v___x_5754_ == 0 {
                        v___f_5755_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___lam__0___boxed as *mut core::ffi::c_void, 9, 2);
                        crate::leanh::lean_closure_set(v___f_5755_, 0, v___x_5753_);
                        crate::leanh::lean_closure_set(v___f_5755_, 1, v___x_5744_);
                        v___x_5756_ = l_Lean_Elab_Command_liftTermElabM___redArg(
                            v___f_5755_,
                            v___y_5739_,
                            v___y_5740_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5756_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5756_, 1);
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___x_5733_);
                            v_a_5757_ = crate::leanh::lean_ctor_get(v___x_5756_, 0);
                            v_isSharedCheck_5764_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5756_)) as u8;
                            if v_isSharedCheck_5764_ == 0 {
                                v___x_5759_ = v___x_5756_;
                                v_isShared_5760_ = v_isSharedCheck_5764_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5757_);
                                crate::leanh::lean_dec(v___x_5756_);
                                v___x_5759_ = crate::leanh::lean_box(0);
                                v_isShared_5760_ = v_isSharedCheck_5764_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5753_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5746_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___closed__0;
                v___x_5747_ = 1usize;
                v___x_5748_ = lean_usize_add(v_i_5737_, v___x_5747_);
                v___x_5749_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9_spec__14(v___x_5733_, v___x_5734_, v_as_5735_, v_sz_5736_, v___x_5748_, v___x_5746_, v___y_5739_, v___y_5740_);
                return v___x_5749_;
            }
            2 => {
                if v_isShared_5760_ == 0 {
                    v___x_5762_ = v___x_5759_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5763_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5763_, 0, v_a_5757_);
                    v___x_5762_ = v_reuseFailAlloc_5763_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5762_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9___boxed(
    mut v___x_5765_: *mut crate::leanh::LeanObject,
    mut v___x_5766_: *mut crate::leanh::LeanObject,
    mut v_as_5767_: *mut crate::leanh::LeanObject,
    mut v_sz_5768_: *mut crate::leanh::LeanObject,
    mut v_i_5769_: *mut crate::leanh::LeanObject,
    mut v_b_5770_: *mut crate::leanh::LeanObject,
    mut v___y_5771_: *mut crate::leanh::LeanObject,
    mut v___y_5772_: *mut crate::leanh::LeanObject,
    mut v___y_5773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_13667__boxed_5774_: u8 = 0;
    let mut v_sz_boxed_5775_: usize = 0;
    let mut v_i_boxed_5776_: usize = 0;
    let mut v_res_5777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_13667__boxed_5774_ = (crate::leanh::lean_unbox(v___x_5766_) as u8);
    v_sz_boxed_5775_ = crate::leanh::lean_unbox_usize(v_sz_5768_);
    crate::leanh::lean_dec(v_sz_5768_);
    v_i_boxed_5776_ = crate::leanh::lean_unbox_usize(v_i_5769_);
    crate::leanh::lean_dec(v_i_5769_);
    v_res_5777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9(v___x_5765_, v___x_13667__boxed_5774_, v_as_5767_, v_sz_boxed_5775_, v_i_boxed_5776_, v_b_5770_, v___y_5771_, v___y_5772_);
    crate::leanh::lean_dec(v___y_5772_);
    crate::leanh::lean_dec_ref(v___y_5771_);
    crate::leanh::lean_dec_ref(v_as_5767_);
    return v_res_5777_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5(
    mut v___x_5778_: *mut crate::leanh::LeanObject,
    mut v___x_5779_: u8,
    mut v_t_5780_: *mut crate::leanh::LeanObject,
    mut v_init_5781_: *mut crate::leanh::LeanObject,
    mut v___y_5782_: *mut crate::leanh::LeanObject,
    mut v___y_5783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5791_: u8 = 0;
    let mut v_a_5792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5799_: usize = 0;
    let mut v___x_5800_: usize = 0;
    let mut v___x_5801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5805_: u8 = 0;
    let mut v_fst_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5815_: u8 = 0;
    let mut v_a_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5819_: u8 = 0;
    let mut v___x_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5823_: u8 = 0;
    let mut v_isSharedCheck_5824_: u8 = 0;
    let mut v_a_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5828_: u8 = 0;
    let mut v___x_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5832_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_5785_ = crate::leanh::lean_ctor_get(v_t_5780_, 0);
                v_tail_5786_ = crate::leanh::lean_ctor_get(v_t_5780_, 1);
                crate::leanh::lean_inc_ref(v___x_5778_);
                v___x_5787_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__8(v_init_5781_, v___x_5778_, v___x_5779_, v_root_5785_, v_init_5781_, v___y_5782_, v___y_5783_);
                if crate::leanh::lean_obj_tag(v___x_5787_) == 0 {
                    v_a_5788_ = crate::leanh::lean_ctor_get(v___x_5787_, 0);
                    v_isSharedCheck_5824_ = (!crate::leanh::lean_is_exclusive(v___x_5787_)) as u8;
                    if v_isSharedCheck_5824_ == 0 {
                        v___x_5790_ = v___x_5787_;
                        v_isShared_5791_ = v_isSharedCheck_5824_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5788_);
                        crate::leanh::lean_dec(v___x_5787_);
                        v___x_5790_ = crate::leanh::lean_box(0);
                        v_isShared_5791_ = v_isSharedCheck_5824_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_5778_);
                    v_a_5825_ = crate::leanh::lean_ctor_get(v___x_5787_, 0);
                    v_isSharedCheck_5832_ = (!crate::leanh::lean_is_exclusive(v___x_5787_)) as u8;
                    if v_isSharedCheck_5832_ == 0 {
                        v___x_5827_ = v___x_5787_;
                        v_isShared_5828_ = v_isSharedCheck_5832_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5825_);
                        crate::leanh::lean_dec(v___x_5787_);
                        v___x_5827_ = crate::leanh::lean_box(0);
                        v_isShared_5828_ = v_isSharedCheck_5832_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5788_) == 0 {
                    crate::leanh::lean_dec_ref(v___x_5778_);
                    v_a_5792_ = crate::leanh::lean_ctor_get(v_a_5788_, 0);
                    crate::leanh::lean_inc(v_a_5792_);
                    crate::leanh::lean_dec_ref_known(v_a_5788_, 1);
                    if v_isShared_5791_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5790_, 0, v_a_5792_);
                        v___x_5794_ = v___x_5790_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5795_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5795_, 0, v_a_5792_);
                        v___x_5794_ = v_reuseFailAlloc_5795_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5790_);
                    v_a_5796_ = crate::leanh::lean_ctor_get(v_a_5788_, 0);
                    crate::leanh::lean_inc(v_a_5796_);
                    crate::leanh::lean_dec_ref_known(v_a_5788_, 1);
                    v___x_5797_ = crate::leanh::lean_box(0);
                    v___x_5798_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5798_, 0, v___x_5797_);
                    crate::leanh::lean_ctor_set(v___x_5798_, 1, v_a_5796_);
                    v_sz_5799_ = lean_array_size(v_tail_5786_);
                    v___x_5800_ = 0usize;
                    v___x_5801_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5_spec__9(v___x_5778_, v___x_5779_, v_tail_5786_, v_sz_5799_, v___x_5800_, v___x_5798_, v___y_5782_, v___y_5783_);
                    if crate::leanh::lean_obj_tag(v___x_5801_) == 0 {
                        v_a_5802_ = crate::leanh::lean_ctor_get(v___x_5801_, 0);
                        v_isSharedCheck_5815_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5801_)) as u8;
                        if v_isSharedCheck_5815_ == 0 {
                            v___x_5804_ = v___x_5801_;
                            v_isShared_5805_ = v_isSharedCheck_5815_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5802_);
                            crate::leanh::lean_dec(v___x_5801_);
                            v___x_5804_ = crate::leanh::lean_box(0);
                            v_isShared_5805_ = v_isSharedCheck_5815_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5816_ = crate::leanh::lean_ctor_get(v___x_5801_, 0);
                        v_isSharedCheck_5823_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5801_)) as u8;
                        if v_isSharedCheck_5823_ == 0 {
                            v___x_5818_ = v___x_5801_;
                            v_isShared_5819_ = v_isSharedCheck_5823_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5816_);
                            crate::leanh::lean_dec(v___x_5801_);
                            v___x_5818_ = crate::leanh::lean_box(0);
                            v_isShared_5819_ = v_isSharedCheck_5823_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5794_;
            }
            3 => {
                v_fst_5806_ = crate::leanh::lean_ctor_get(v_a_5802_, 0);
                if crate::leanh::lean_obj_tag(v_fst_5806_) == 0 {
                    v_snd_5807_ = crate::leanh::lean_ctor_get(v_a_5802_, 1);
                    crate::leanh::lean_inc(v_snd_5807_);
                    crate::leanh::lean_dec(v_a_5802_);
                    if v_isShared_5805_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5804_, 0, v_snd_5807_);
                        v___x_5809_ = v___x_5804_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5810_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5810_, 0, v_snd_5807_);
                        v___x_5809_ = v_reuseFailAlloc_5810_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_5806_);
                    crate::leanh::lean_dec(v_a_5802_);
                    v_val_5811_ = crate::leanh::lean_ctor_get(v_fst_5806_, 0);
                    crate::leanh::lean_inc(v_val_5811_);
                    crate::leanh::lean_dec_ref_known(v_fst_5806_, 1);
                    if v_isShared_5805_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5804_, 0, v_val_5811_);
                        v___x_5813_ = v___x_5804_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5814_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5814_, 0, v_val_5811_);
                        v___x_5813_ = v_reuseFailAlloc_5814_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_5809_;
            }
            5 => {
                return v___x_5813_;
            }
            6 => {
                if v_isShared_5819_ == 0 {
                    v___x_5821_ = v___x_5818_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5822_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5822_, 0, v_a_5816_);
                    v___x_5821_ = v_reuseFailAlloc_5822_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5821_;
            }
            8 => {
                if v_isShared_5828_ == 0 {
                    v___x_5830_ = v___x_5827_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5831_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5831_, 0, v_a_5825_);
                    v___x_5830_ = v_reuseFailAlloc_5831_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5830_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5___boxed(
    mut v___x_5833_: *mut crate::leanh::LeanObject,
    mut v___x_5834_: *mut crate::leanh::LeanObject,
    mut v_t_5835_: *mut crate::leanh::LeanObject,
    mut v_init_5836_: *mut crate::leanh::LeanObject,
    mut v___y_5837_: *mut crate::leanh::LeanObject,
    mut v___y_5838_: *mut crate::leanh::LeanObject,
    mut v___y_5839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_13730__boxed_5840_: u8 = 0;
    let mut v_res_5841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_13730__boxed_5840_ = (crate::leanh::lean_unbox(v___x_5834_) as u8);
    v_res_5841_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5(v___x_5833_, v___x_13730__boxed_5840_, v_t_5835_, v_init_5836_, v___y_5837_, v___y_5838_);
    crate::leanh::lean_dec(v___y_5838_);
    crate::leanh::lean_dec_ref(v___y_5837_);
    crate::leanh::lean_dec_ref(v_t_5835_);
    return v_res_5841_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0___redArg(
    mut v_o_5842_: *mut crate::leanh::LeanObject,
    mut v___y_5843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_linterSets_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5845_ = lean_st_ref_get(v___y_5843_);
    v_env_5846_ = crate::leanh::lean_ctor_get(v___x_5845_, 0);
    crate::leanh::lean_inc_ref(v_env_5846_);
    crate::leanh::lean_dec(v___x_5845_);
    v___x_5847_ = l_Lean_Linter_linterSetsExt;
    v_toEnvExtension_5848_ = crate::leanh::lean_ctor_get(v___x_5847_, 0);
    v_asyncMode_5849_ = crate::leanh::lean_ctor_get(v_toEnvExtension_5848_, 2);
    v___x_5850_ = crate::leanh::lean_box(1);
    v___x_5851_ = crate::leanh::lean_box(0);
    v_linterSets_5852_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_5850_,
        v___x_5847_,
        v_env_5846_,
        v_asyncMode_5849_,
        v___x_5851_,
    );
    v___x_5853_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5853_, 0, v_o_5842_);
    crate::leanh::lean_ctor_set(v___x_5853_, 1, v_linterSets_5852_);
    v___x_5854_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5854_, 0, v___x_5853_);
    return v___x_5854_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0___redArg___boxed(
    mut v_o_5855_: *mut crate::leanh::LeanObject,
    mut v___y_5856_: *mut crate::leanh::LeanObject,
    mut v___y_5857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5858_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0___redArg(v_o_5855_, v___y_5856_);
    crate::leanh::lean_dec(v___y_5856_);
    return v_res_5858_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0(
    mut v___y_5859_: *mut crate::leanh::LeanObject,
    mut v___y_5860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_5866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5862_ = lean_st_ref_get(v___y_5860_);
    v_scopes_5863_ = crate::leanh::lean_ctor_get(v___x_5862_, 2);
    crate::leanh::lean_inc(v_scopes_5863_);
    crate::leanh::lean_dec(v___x_5862_);
    v___x_5864_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_5865_ = l_List_head_x21___redArg(v___x_5864_, v_scopes_5863_);
    crate::leanh::lean_dec(v_scopes_5863_);
    v_opts_5866_ = crate::leanh::lean_ctor_get(v___x_5865_, 1);
    crate::leanh::lean_inc_ref(v_opts_5866_);
    crate::leanh::lean_dec(v___x_5865_);
    v___x_5867_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0___redArg(v_opts_5866_, v___y_5860_);
    return v___x_5867_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0___boxed(
    mut v___y_5868_: *mut crate::leanh::LeanObject,
    mut v___y_5869_: *mut crate::leanh::LeanObject,
    mut v___y_5870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5871_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0(v___y_5868_, v___y_5869_);
    crate::leanh::lean_dec(v___y_5869_);
    crate::leanh::lean_dec_ref(v___y_5868_);
    return v_res_5871_;
}
pub unsafe fn l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___lam__0(
    mut v_x_5872_: *mut crate::leanh::LeanObject,
    mut v___y_5873_: *mut crate::leanh::LeanObject,
    mut v___y_5874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5880_: u8 = 0;
    let mut v___x_5881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5883_: u8 = 0;
    let mut v___x_5884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: u8 = 0;
    let mut v___x_5891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5899_: u8 = 0;
    let mut v___x_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5903_: u8 = 0;
    let mut v_unused_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: u8 = 0;
    let mut v_infoState_5911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_5912_: u8 = 0;
    let mut v_isSharedCheck_5913_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5876_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0(v___y_5873_, v___y_5874_);
                v_a_5877_ = crate::leanh::lean_ctor_get(v___x_5876_, 0);
                v_isSharedCheck_5913_ = (!crate::leanh::lean_is_exclusive(v___x_5876_)) as u8;
                if v_isSharedCheck_5913_ == 0 {
                    v___x_5879_ = v___x_5876_;
                    v_isShared_5880_ = v_isSharedCheck_5913_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5877_);
                    crate::leanh::lean_dec(v___x_5876_);
                    v___x_5879_ = crate::leanh::lean_box(0);
                    v_isShared_5880_ = v_isSharedCheck_5913_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5881_ = lean_st_ref_get(v___y_5874_);
                v___x_5909_ = l_Lean_Linter_Extra_linter_extra_unusedDecidableInType;
                v___x_5910_ = l_Lean_Linter_getLinterValueExtra(v___x_5909_, v_a_5877_);
                crate::leanh::lean_dec(v_a_5877_);
                if v___x_5910_ == 0 {
                    crate::leanh::lean_dec(v___x_5881_);
                    v___y_5883_ = v___x_5910_;
                    state = 2;
                    continue;
                } else {
                    v_infoState_5911_ = crate::leanh::lean_ctor_get(v___x_5881_, 8);
                    crate::leanh::lean_inc_ref(v_infoState_5911_);
                    crate::leanh::lean_dec(v___x_5881_);
                    v_enabled_5912_ = crate::leanh::lean_ctor_get_uint8(
                        v_infoState_5911_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    crate::leanh::lean_dec_ref(v_infoState_5911_);
                    v___y_5883_ = v_enabled_5912_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_5883_ == 0 {
                    v___x_5884_ = crate::leanh::lean_box(0);
                    if v_isShared_5880_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5879_, 0, v___x_5884_);
                        v___x_5886_ = v___x_5879_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5887_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5887_, 0, v___x_5884_);
                        v___x_5886_ = v_reuseFailAlloc_5887_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_5888_ = lean_st_ref_get(v___y_5874_);
                    v_messages_5889_ = crate::leanh::lean_ctor_get(v___x_5888_, 1);
                    crate::leanh::lean_inc_ref(v_messages_5889_);
                    crate::leanh::lean_dec(v___x_5888_);
                    v___x_5890_ = l_Lean_MessageLog_hasErrors(v_messages_5889_);
                    crate::leanh::lean_dec_ref(v_messages_5889_);
                    if v___x_5890_ == 0 {
                        crate::leanh::lean_del_object(v___x_5879_);
                        v___x_5891_ = lean_st_ref_get(v___y_5874_);
                        v___x_5892_ = l_Lean_Elab_getInfoTrees___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__1___redArg(v___y_5874_);
                        v_a_5893_ = crate::leanh::lean_ctor_get(v___x_5892_, 0);
                        crate::leanh::lean_inc(v_a_5893_);
                        crate::leanh::lean_dec_ref(v___x_5892_);
                        v_env_5894_ = crate::leanh::lean_ctor_get(v___x_5891_, 0);
                        crate::leanh::lean_inc_ref(v_env_5894_);
                        crate::leanh::lean_dec(v___x_5891_);
                        v___x_5895_ = crate::leanh::lean_box(0);
                        v___x_5896_ = l_Lean_PersistentArray_forIn___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__5(v_env_5894_, v___x_5890_, v_a_5893_, v___x_5895_, v___y_5873_, v___y_5874_);
                        crate::leanh::lean_dec(v_a_5893_);
                        if crate::leanh::lean_obj_tag(v___x_5896_) == 0 {
                            v_isSharedCheck_5903_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5896_)) as u8;
                            if v_isSharedCheck_5903_ == 0 {
                                v_unused_5904_ = crate::leanh::lean_ctor_get(v___x_5896_, 0);
                                crate::leanh::lean_dec(v_unused_5904_);
                                v___x_5898_ = v___x_5896_;
                                v_isShared_5899_ = v_isSharedCheck_5903_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_5896_);
                                v___x_5898_ = crate::leanh::lean_box(0);
                                v_isShared_5899_ = v_isSharedCheck_5903_;
                                state = 4;
                                continue;
                            }
                        } else {
                            return v___x_5896_;
                        }
                    } else {
                        v___x_5905_ = crate::leanh::lean_box(0);
                        if v_isShared_5880_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5879_, 0, v___x_5905_);
                            v___x_5907_ = v___x_5879_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_5908_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5908_, 0, v___x_5905_);
                            v___x_5907_ = v_reuseFailAlloc_5908_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_5886_;
            }
            4 => {
                if v_isShared_5899_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5898_, 0, v___x_5895_);
                    v___x_5901_ = v___x_5898_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5902_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5902_, 0, v___x_5895_);
                    v___x_5901_ = v_reuseFailAlloc_5902_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5901_;
            }
            6 => {
                return v___x_5907_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___lam__0___boxed(
    mut v_x_5914_: *mut crate::leanh::LeanObject,
    mut v___y_5915_: *mut crate::leanh::LeanObject,
    mut v___y_5916_: *mut crate::leanh::LeanObject,
    mut v___y_5917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5918_ = l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter___lam__0(
        v_x_5914_,
        v___y_5915_,
        v___y_5916_,
    );
    crate::leanh::lean_dec(v___y_5916_);
    crate::leanh::lean_dec_ref(v___y_5915_);
    crate::leanh::lean_dec(v_x_5914_);
    return v_res_5918_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0(
    mut v_o_5934_: *mut crate::leanh::LeanObject,
    mut v___y_5935_: *mut crate::leanh::LeanObject,
    mut v___y_5936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5938_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0___redArg(v_o_5934_, v___y_5936_);
    return v___x_5938_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0___boxed(
    mut v_o_5939_: *mut crate::leanh::LeanObject,
    mut v___y_5940_: *mut crate::leanh::LeanObject,
    mut v___y_5941_: *mut crate::leanh::LeanObject,
    mut v___y_5942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5943_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__0_spec__0(v_o_5939_, v___y_5940_, v___y_5941_);
    crate::leanh::lean_dec(v___y_5941_);
    crate::leanh::lean_dec_ref(v___y_5940_);
    return v_res_5943_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4(
    mut v_as_5944_: *mut crate::leanh::LeanObject,
    mut v_as_x27_5945_: *mut crate::leanh::LeanObject,
    mut v_b_5946_: *mut crate::leanh::LeanObject,
    mut v_a_5947_: *mut crate::leanh::LeanObject,
    mut v___y_5948_: *mut crate::leanh::LeanObject,
    mut v___y_5949_: *mut crate::leanh::LeanObject,
    mut v___y_5950_: *mut crate::leanh::LeanObject,
    mut v___y_5951_: *mut crate::leanh::LeanObject,
    mut v___y_5952_: *mut crate::leanh::LeanObject,
    mut v___y_5953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5955_ = l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___redArg(v_as_x27_5945_, v_b_5946_, v___y_5948_, v___y_5949_, v___y_5950_, v___y_5951_, v___y_5952_, v___y_5953_);
    return v___x_5955_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4___boxed(
    mut v_as_5956_: *mut crate::leanh::LeanObject,
    mut v_as_x27_5957_: *mut crate::leanh::LeanObject,
    mut v_b_5958_: *mut crate::leanh::LeanObject,
    mut v_a_5959_: *mut crate::leanh::LeanObject,
    mut v___y_5960_: *mut crate::leanh::LeanObject,
    mut v___y_5961_: *mut crate::leanh::LeanObject,
    mut v___y_5962_: *mut crate::leanh::LeanObject,
    mut v___y_5963_: *mut crate::leanh::LeanObject,
    mut v___y_5964_: *mut crate::leanh::LeanObject,
    mut v___y_5965_: *mut crate::leanh::LeanObject,
    mut v___y_5966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5967_ = l_List_forIn_x27_loop___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__4(v_as_5956_, v_as_x27_5957_, v_b_5958_, v_a_5959_, v___y_5960_, v___y_5961_, v___y_5962_, v___y_5963_, v___y_5964_, v___y_5965_);
    crate::leanh::lean_dec(v___y_5965_);
    crate::leanh::lean_dec_ref(v___y_5964_);
    crate::leanh::lean_dec(v___y_5963_);
    crate::leanh::lean_dec_ref(v___y_5962_);
    crate::leanh::lean_dec(v___y_5961_);
    crate::leanh::lean_dec_ref(v___y_5960_);
    crate::leanh::lean_dec(v_as_x27_5957_);
    crate::leanh::lean_dec(v_as_5956_);
    return v_res_5967_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__4_spec__5(
    mut v_o_5968_: *mut crate::leanh::LeanObject,
    mut v___y_5969_: *mut crate::leanh::LeanObject,
    mut v___y_5970_: *mut crate::leanh::LeanObject,
    mut v___y_5971_: *mut crate::leanh::LeanObject,
    mut v___y_5972_: *mut crate::leanh::LeanObject,
    mut v___y_5973_: *mut crate::leanh::LeanObject,
    mut v___y_5974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5976_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__4_spec__5___redArg(v_o_5968_, v___y_5974_);
    return v___x_5976_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__4_spec__5___boxed(
    mut v_o_5977_: *mut crate::leanh::LeanObject,
    mut v___y_5978_: *mut crate::leanh::LeanObject,
    mut v___y_5979_: *mut crate::leanh::LeanObject,
    mut v___y_5980_: *mut crate::leanh::LeanObject,
    mut v___y_5981_: *mut crate::leanh::LeanObject,
    mut v___y_5982_: *mut crate::leanh::LeanObject,
    mut v___y_5983_: *mut crate::leanh::LeanObject,
    mut v___y_5984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5985_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__4_spec__5(v_o_5977_, v___y_5978_, v___y_5979_, v___y_5980_, v___y_5981_, v___y_5982_, v___y_5983_);
    crate::leanh::lean_dec(v___y_5983_);
    crate::leanh::lean_dec_ref(v___y_5982_);
    crate::leanh::lean_dec(v___y_5981_);
    crate::leanh::lean_dec_ref(v___y_5980_);
    crate::leanh::lean_dec(v___y_5979_);
    crate::leanh::lean_dec_ref(v___y_5978_);
    return v_res_5985_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10(
    mut v_ref_5986_: *mut crate::leanh::LeanObject,
    mut v_msgData_5987_: *mut crate::leanh::LeanObject,
    mut v_severity_5988_: u8,
    mut v_isSilent_5989_: u8,
    mut v___y_5990_: *mut crate::leanh::LeanObject,
    mut v___y_5991_: *mut crate::leanh::LeanObject,
    mut v___y_5992_: *mut crate::leanh::LeanObject,
    mut v___y_5993_: *mut crate::leanh::LeanObject,
    mut v___y_5994_: *mut crate::leanh::LeanObject,
    mut v___y_5995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5997_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___redArg(v_ref_5986_, v_msgData_5987_, v_severity_5988_, v_isSilent_5989_, v___y_5992_, v___y_5993_, v___y_5994_, v___y_5995_);
    return v___x_5997_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10___boxed(
    mut v_ref_5998_: *mut crate::leanh::LeanObject,
    mut v_msgData_5999_: *mut crate::leanh::LeanObject,
    mut v_severity_6000_: *mut crate::leanh::LeanObject,
    mut v_isSilent_6001_: *mut crate::leanh::LeanObject,
    mut v___y_6002_: *mut crate::leanh::LeanObject,
    mut v___y_6003_: *mut crate::leanh::LeanObject,
    mut v___y_6004_: *mut crate::leanh::LeanObject,
    mut v___y_6005_: *mut crate::leanh::LeanObject,
    mut v___y_6006_: *mut crate::leanh::LeanObject,
    mut v___y_6007_: *mut crate::leanh::LeanObject,
    mut v___y_6008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_6009_: u8 = 0;
    let mut v_isSilent_boxed_6010_: u8 = 0;
    let mut v_res_6011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_6009_ = (crate::leanh::lean_unbox(v_severity_6000_) as u8);
    v_isSilent_boxed_6010_ = (crate::leanh::lean_unbox(v_isSilent_6001_) as u8);
    v_res_6011_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIfExtra___at___00Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter_spec__3_spec__5_spec__7_spec__10(v_ref_5998_, v_msgData_5999_, v_severity_boxed_6009_, v_isSilent_boxed_6010_, v___y_6002_, v___y_6003_, v___y_6004_, v___y_6005_, v___y_6006_, v___y_6007_);
    crate::leanh::lean_dec(v___y_6007_);
    crate::leanh::lean_dec_ref(v___y_6006_);
    crate::leanh::lean_dec(v___y_6005_);
    crate::leanh::lean_dec_ref(v___y_6004_);
    crate::leanh::lean_dec(v___y_6003_);
    crate::leanh::lean_dec_ref(v___y_6002_);
    crate::leanh::lean_dec(v_ref_5998_);
    return v_res_6011_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_1360886744____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6013_ = l_Lean_Linter_Extra_UnusedDecidableInType_unusedDecidableInTypeLinter;
    v___x_6014_ = l_Lean_Elab_Command_addLinter(v___x_6013_);
    return v___x_6014_;
}
pub unsafe fn l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_1360886744____hygCtx___hyg_2____boxed(
    mut v_a_6015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6016_ = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_1360886744____hygCtx___hyg_2_();
    return v_res_6016_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Linter_Extra_UnusedDecidableInType(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Linter_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_ForEachExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sorry(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_PrivateName(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_InfoUtils(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_3995904732____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Linter_Extra_linter_extra_unusedDecidableInType =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Linter_Extra_linter_extra_unusedDecidableInType);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Linter_Extra_UnusedDecidableInType_0__Lean_Linter_Extra_UnusedDecidableInType_initFn_00___x40_Lean_Linter_Extra_UnusedDecidableInType_1360886744____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Linter_Extra_UnusedDecidableInType(
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
pub unsafe fn initialize_Lean_Linter_Extra_UnusedDecidableInType(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Linter_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_ForEachExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sorry(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_PrivateName(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Server_InfoUtils(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Extra_UnusedDecidableInType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Linter_Extra_UnusedDecidableInType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Linter_Extra_UnusedDecidableInType(builtin);
}
