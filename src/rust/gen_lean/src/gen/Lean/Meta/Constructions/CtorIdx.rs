// Lean compiler output
// Module: Lean.Meta.Constructions.CtorIdx
// Imports: Lean.Meta.Basic Lean.AddDecl Lean.Meta.CompletionName Lean.Linter.Deprecated
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_str___override, l_Lean_replaceRef, l_List_lengthTR___redArg,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::AddDecl::{
    initialize_Lean_AddDecl, l_Lean_addDecl, runtime_initialize_Lean_AddDecl,
};
use crate::r#gen::Lean::Attributes::l_Lean_ParametricAttribute_setParam___redArg;
use crate::r#gen::Lean::AuxRecursor::l_Lean_mkCasesOnName;
use crate::r#gen::Lean::Compiler::MetaAttr::{l_Lean_isMarkedMeta, l_Lean_markMeta};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
    l_Lean_compileDecl, l_Lean_compileDecls, l_Lean_enableRealizationsForConst, l_Lean_mkArrow,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::{l_Lean_Options_empty, lean_register_option};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::{
    l_Lean_ConstantInfo_levelParams, l_Lean_InductiveVal_numCtors,
    l_Lean_InductiveVal_numTypeFormers,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_AsyncConstantInfo_toConstantInfo, l_Lean_Environment_contains,
    l_Lean_Environment_find_x3f, l_Lean_Environment_findAsync_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_hasUnsafe,
    l_Lean_Environment_header, l_Lean_Environment_setExporting,
    l_Lean_EnvironmentHeader_moduleNames, l_Lean_getMaxHeight,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_fvarId_x21, l_Lean_Expr_isProp, l_Lean_mkAppN,
    l_Lean_mkConst, l_Lean_mkRawNatLit,
};
use crate::r#gen::Lean::Level::{l_Lean_Level_succ___override, l_Lean_mkLevelParam};
use crate::r#gen::Lean::Linter::Deprecated::{
    initialize_Lean_Linter_Deprecated, l_Lean_Linter_deprecatedAttr,
    runtime_initialize_Lean_Linter_Deprecated,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_indentD, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp,
    l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__0___boxed,
    l_Lean_Meta_instMonadMetaM___lam__1___boxed, l_Lean_Meta_instantiateForall,
    l_Lean_Meta_mapErrorImp___redArg, l_Lean_Meta_mkForallFVars, l_Lean_Meta_mkLambdaFVars,
    l_Lean_Meta_setInlineAttribute, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::CompletionName::{
    initialize_Lean_Meta_CompletionName, l_Lean_Meta_addToCompletionBlackList,
    runtime_initialize_Lean_Meta_CompletionName,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isPropFormerType;
use crate::r#gen::Lean::Modifiers::l_Lean_addProtected;
use crate::r#gen::Lean::MonadEnv::l_Lean_isInductiveCore_x3f;
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ReducibilityAttrs::l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore;
use crate::ffi::{
    lean_array_size, lean_array_uget, lean_array_uset,
};
use crate::ffi::{
    lean_uint32_add, lean_usize_add, lean_usize_dec_lt,
};
use crate::ffi::{
    lean_array_get, lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_panic_fn_borrowed, lean_string_dec_eq,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [103, 101, 110, 67, 116, 111, 114, 73, 100, 120, 0]};
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,14568703005891071609 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<57> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 57, m_capacity: 57, m_length: 56, m_data: [103, 101, 110, 101, 114, 97, 116, 101, 32, 116, 104, 101, 32, 96, 67, 116, 111, 114, 73, 100, 120, 96, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 32, 102, 111, 114, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 100, 97, 116, 97, 116, 121, 112, 101, 115, 0]};
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,13556645696814629918 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [67, 111, 110, 115, 116, 114, 117, 99, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,6298619751691480032 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 116, 111, 114, 73, 100, 120, 0]};
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16920199611135063957 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,14740007710918899200 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,8814159201242699910 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Meta_Constructions_CtorIdx_0__genCtorIdx:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_mkToCtorIdxName___closed__0_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [116, 111, 67, 116, 111, 114, 73, 100, 120, 0],
    };
static mut l_mkToCtorIdxName___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_mkToCtorIdxName___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_mkCtorIdxName___closed__0_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [99, 116, 111, 114, 73, 100, 120, 0],
    };
static mut l_mkCtorIdxName___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_mkCtorIdxName___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00mkCtorIdx_spec__13___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00mkCtorIdx_spec__13___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00mkCtorIdx_spec__13___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__0_value:
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
    m_data: [96, 0],
};
static mut l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__2_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116,
        111, 114, 0,
    ],
};
static mut l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__4_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [76, 101, 97, 110, 46, 77, 111, 110, 97, 100, 69, 110, 118, 0],
};
static mut l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__5_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [76, 101, 97, 110, 46, 105, 115, 67, 116, 111, 114, 63, 0],
};
static mut l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__6_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115,
        32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
    ],
};
static mut l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_mkCtorIdx___lam__0___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_mkCtorIdx___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__6_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__8_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__10_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__12_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__14_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__16_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__18_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_mkCtorIdx___lam__1___closed__0_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [50, 48, 50, 53, 45, 48, 56, 45, 50, 53, 0],
    };
static mut l_mkCtorIdx___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_mkCtorIdx___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_mkCtorIdx___lam__1___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [core::ptr::addr_of!(l_mkCtorIdx___lam__1___closed__0_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_mkCtorIdx___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_mkCtorIdx___lam__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_mkCtorIdx___lam__1___closed__2_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [120, 0],
    };
static mut l_mkCtorIdx___lam__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_mkCtorIdx___lam__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_mkCtorIdx___lam__1___closed__3_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_mkCtorIdx___lam__1___closed__2_value)
                as *mut crate::leanh::LeanObject,
            13655884332201764339 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_mkCtorIdx___lam__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_mkCtorIdx___lam__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_mkCtorIdx___lam__2___closed__0_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [78, 97, 116, 0],
    };
static mut l_mkCtorIdx___lam__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_mkCtorIdx___lam__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_mkCtorIdx___lam__2___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_mkCtorIdx___lam__2___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11442535297760353691 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_mkCtorIdx___lam__2___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_mkCtorIdx___lam__2___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_mkCtorIdx___lam__3___closed__0_value: crate::leanh::LeanStringObject<32> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67, 111, 110, 115, 116, 114, 117, 99, 116,
            105, 111, 110, 115, 46, 67, 116, 111, 114, 73, 100, 120, 0,
        ],
    };
static mut l_mkCtorIdx___lam__3___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_mkCtorIdx___lam__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_mkCtorIdx___lam__3___closed__1_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [109, 107, 67, 116, 111, 114, 73, 100, 120, 0],
    };
static mut l_mkCtorIdx___lam__3___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_mkCtorIdx___lam__3___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_mkCtorIdx___lam__3___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_mkCtorIdx___lam__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_mkCtorIdx___closed__0_value: crate::leanh::LeanStringObject<38> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 38,
        m_capacity: 38,
        m_length: 37,
        m_data: [
            102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 99, 111, 110, 115, 116, 114, 117, 99,
            116, 32, 96, 84, 46, 99, 116, 111, 114, 73, 100, 120, 96, 32, 102, 111, 114, 32, 96, 0,
        ],
    };
static mut l_mkCtorIdx___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_mkCtorIdx___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_mkCtorIdx___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_mkCtorIdx___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_mkCtorIdx___closed__2_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [96, 58, 0],
    };
static mut l_mkCtorIdx___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_mkCtorIdx___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_mkCtorIdx___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_mkCtorIdx___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(
    mut v_name_2379_: *mut crate::leanh::LeanObject,
    mut v_decl_2380_: *mut crate::leanh::LeanObject,
    mut v_ref_2381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: u8 = 0;
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2392_: u8 = 0;
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2397_: u8 = 0;
    let mut v_unused_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2402_: u8 = 0;
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2406_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_2383_ = crate::leanh::lean_ctor_get(v_decl_2380_, 0);
                v_descr_2384_ = crate::leanh::lean_ctor_get(v_decl_2380_, 1);
                v_deprecation_x3f_2385_ = crate::leanh::lean_ctor_get(v_decl_2380_, 2);
                v___x_2386_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_2387_ = (crate::leanh::lean_unbox(v_defValue_2383_) as u8);
                crate::leanh::lean_ctor_set_uint8(v___x_2386_, 0 as u32, v___x_2387_);
                crate::leanh::lean_inc(v_deprecation_x3f_2385_);
                crate::leanh::lean_inc_ref(v_descr_2384_);
                crate::leanh::lean_inc_n(v_name_2379_, 2);
                v___x_2388_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2388_, 0, v_name_2379_);
                crate::leanh::lean_ctor_set(v___x_2388_, 1, v_ref_2381_);
                crate::leanh::lean_ctor_set(v___x_2388_, 2, v___x_2386_);
                crate::leanh::lean_ctor_set(v___x_2388_, 3, v_descr_2384_);
                crate::leanh::lean_ctor_set(v___x_2388_, 4, v_deprecation_x3f_2385_);
                v___x_2389_ = lean_register_option(v_name_2379_, v___x_2388_);
                if crate::leanh::lean_obj_tag(v___x_2389_) == 0 {
                    v_isSharedCheck_2397_ = (!crate::leanh::lean_is_exclusive(v___x_2389_)) as u8;
                    if v_isSharedCheck_2397_ == 0 {
                        v_unused_2398_ = crate::leanh::lean_ctor_get(v___x_2389_, 0);
                        crate::leanh::lean_dec(v_unused_2398_);
                        v___x_2391_ = v___x_2389_;
                        v_isShared_2392_ = v_isSharedCheck_2397_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2389_);
                        v___x_2391_ = crate::leanh::lean_box(0);
                        v_isShared_2392_ = v_isSharedCheck_2397_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_2379_);
                    v_a_2399_ = crate::leanh::lean_ctor_get(v___x_2389_, 0);
                    v_isSharedCheck_2406_ = (!crate::leanh::lean_is_exclusive(v___x_2389_)) as u8;
                    if v_isSharedCheck_2406_ == 0 {
                        v___x_2401_ = v___x_2389_;
                        v_isShared_2402_ = v_isSharedCheck_2406_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2399_);
                        crate::leanh::lean_dec(v___x_2389_);
                        v___x_2401_ = crate::leanh::lean_box(0);
                        v_isShared_2402_ = v_isSharedCheck_2406_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_2383_);
                v___x_2393_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2393_, 0, v_name_2379_);
                crate::leanh::lean_ctor_set(v___x_2393_, 1, v_defValue_2383_);
                if v_isShared_2392_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2391_, 0, v___x_2393_);
                    v___x_2395_ = v___x_2391_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2396_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2393_);
                    v___x_2395_ = v_reuseFailAlloc_2396_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2395_;
            }
            3 => {
                if v_isShared_2402_ == 0 {
                    v___x_2404_ = v___x_2401_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2405_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2399_);
                    v___x_2404_ = v_reuseFailAlloc_2405_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2404_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_2407_: *mut crate::leanh::LeanObject,
    mut v_decl_2408_: *mut crate::leanh::LeanObject,
    mut v_ref_2409_: *mut crate::leanh::LeanObject,
    mut v_a_2410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2411_ = l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(v_name_2407_, v_decl_2408_, v_ref_2409_);
    crate::leanh::lean_dec_ref(v_decl_2408_);
    return v_res_2411_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2448_ = l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_;
    v___x_2449_ = l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_;
    v___x_2450_ = l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_;
    v___x_2451_ = l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(v___x_2448_, v___x_2449_, v___x_2450_);
    return v___x_2451_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4____boxed(
    mut v_a_2452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2453_ = l___private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_();
    return v_res_2453_;
}
pub unsafe fn l_mkToCtorIdxName(
    mut v_indName_2455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2456_ = l_mkToCtorIdxName___closed__0;
    v___x_2457_ = l_Lean_Name_str___override(v_indName_2455_, v___x_2456_);
    return v___x_2457_;
}
pub unsafe fn l_mkCtorIdxName(
    mut v_indName_2459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2460_ = l_mkCtorIdxName___closed__0;
    v___x_2461_ = l_Lean_Name_str___override(v_indName_2459_, v___x_2460_);
    return v___x_2461_;
}
pub unsafe fn l_isCtorIdxCore_x3f(
    mut v_env_2462_: *mut crate::leanh::LeanObject,
    mut v_declName_2463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_declName_2463_) == 1 {
        let mut v_pre_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_str_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2467_: u8 = 0;
        v_pre_2464_ = crate::leanh::lean_ctor_get(v_declName_2463_, 0);
        crate::leanh::lean_inc(v_pre_2464_);
        v_str_2465_ = crate::leanh::lean_ctor_get(v_declName_2463_, 1);
        crate::leanh::lean_inc_ref(v_str_2465_);
        crate::leanh::lean_dec_ref_known(v_declName_2463_, 2);
        v___x_2466_ = l_mkCtorIdxName___closed__0;
        v___x_2467_ = lean_string_dec_eq(v_str_2465_, v___x_2466_);
        crate::leanh::lean_dec_ref(v_str_2465_);
        if v___x_2467_ == 0 {
            let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_pre_2464_);
            crate::leanh::lean_dec_ref(v_env_2462_);
            v___x_2468_ = crate::leanh::lean_box(0);
            return v___x_2468_;
        } else {
            let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2469_ = l_Lean_isInductiveCore_x3f(v_env_2462_, v_pre_2464_);
            return v___x_2469_;
        }
    } else {
        let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_declName_2463_);
        crate::leanh::lean_dec_ref(v_env_2462_);
        v___x_2470_ = crate::leanh::lean_box(0);
        return v___x_2470_;
    }
}
pub unsafe fn l_isCtorIdx_x3f___redArg(
    mut v_declName_2471_: *mut crate::leanh::LeanObject,
    mut v_a_2472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2474_ = lean_st_ref_get(v_a_2472_);
    v_env_2475_ = crate::leanh::lean_ctor_get(v___x_2474_, 0);
    crate::leanh::lean_inc_ref(v_env_2475_);
    crate::leanh::lean_dec(v___x_2474_);
    v___x_2476_ = l_isCtorIdxCore_x3f(v_env_2475_, v_declName_2471_);
    v___x_2477_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2477_, 0, v___x_2476_);
    return v___x_2477_;
}
pub unsafe fn l_isCtorIdx_x3f___redArg___boxed(
    mut v_declName_2478_: *mut crate::leanh::LeanObject,
    mut v_a_2479_: *mut crate::leanh::LeanObject,
    mut v_a_2480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2481_ = l_isCtorIdx_x3f___redArg(v_declName_2478_, v_a_2479_);
    crate::leanh::lean_dec(v_a_2479_);
    return v_res_2481_;
}
pub unsafe fn l_isCtorIdx_x3f(
    mut v_declName_2482_: *mut crate::leanh::LeanObject,
    mut v_a_2483_: *mut crate::leanh::LeanObject,
    mut v_a_2484_: *mut crate::leanh::LeanObject,
    mut v_a_2485_: *mut crate::leanh::LeanObject,
    mut v_a_2486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2488_ = l_isCtorIdx_x3f___redArg(v_declName_2482_, v_a_2486_);
    return v___x_2488_;
}
pub unsafe fn l_isCtorIdx_x3f___boxed(
    mut v_declName_2489_: *mut crate::leanh::LeanObject,
    mut v_a_2490_: *mut crate::leanh::LeanObject,
    mut v_a_2491_: *mut crate::leanh::LeanObject,
    mut v_a_2492_: *mut crate::leanh::LeanObject,
    mut v_a_2493_: *mut crate::leanh::LeanObject,
    mut v_a_2494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2495_ = l_isCtorIdx_x3f(v_declName_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_);
    crate::leanh::lean_dec(v_a_2493_);
    crate::leanh::lean_dec_ref(v_a_2492_);
    crate::leanh::lean_dec(v_a_2491_);
    crate::leanh::lean_dec_ref(v_a_2490_);
    return v_res_2495_;
}
pub unsafe fn l_Lean_Option_get___at___00mkCtorIdx_spec__0(
    mut v_opts_2496_: *mut crate::leanh::LeanObject,
    mut v_opt_2497_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_2498_ = crate::leanh::lean_ctor_get(v_opt_2497_, 0);
    v_defValue_2499_ = crate::leanh::lean_ctor_get(v_opt_2497_, 1);
    v_map_2500_ = crate::leanh::lean_ctor_get(v_opts_2496_, 0);
    v___x_2501_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2500_,
            v_name_2498_,
        );
    if crate::leanh::lean_obj_tag(v___x_2501_) == 0 {
        let mut v___x_2502_: u8 = 0;
        v___x_2502_ = (crate::leanh::lean_unbox(v_defValue_2499_) as u8);
        return v___x_2502_;
    } else {
        let mut v_val_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2503_ = crate::leanh::lean_ctor_get(v___x_2501_, 0);
        crate::leanh::lean_inc(v_val_2503_);
        crate::leanh::lean_dec_ref_known(v___x_2501_, 1);
        if crate::leanh::lean_obj_tag(v_val_2503_) == 1 {
            let mut v_v_2504_: u8 = 0;
            v_v_2504_ = crate::leanh::lean_ctor_get_uint8(v_val_2503_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_2503_, 0);
            return v_v_2504_;
        } else {
            let mut v___x_2505_: u8 = 0;
            crate::leanh::lean_dec(v_val_2503_);
            v___x_2505_ = (crate::leanh::lean_unbox(v_defValue_2499_) as u8);
            return v___x_2505_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00mkCtorIdx_spec__0___boxed(
    mut v_opts_2506_: *mut crate::leanh::LeanObject,
    mut v_opt_2507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2508_: u8 = 0;
    let mut v_r_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2508_ = l_Lean_Option_get___at___00mkCtorIdx_spec__0(v_opts_2506_, v_opt_2507_);
    crate::leanh::lean_dec_ref(v_opt_2507_);
    crate::leanh::lean_dec_ref(v_opts_2506_);
    v_r_2509_ = crate::leanh::lean_box((v_res_2508_) as usize);
    return v_r_2509_;
}
pub unsafe fn l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg(
    mut v_constName_2510_: *mut crate::leanh::LeanObject,
    mut v_skipRealize_2511_: u8,
    mut v___y_2512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: u8 = 0;
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2514_ = lean_st_ref_get(v___y_2512_);
    v_env_2515_ = crate::leanh::lean_ctor_get(v___x_2514_, 0);
    crate::leanh::lean_inc_ref(v_env_2515_);
    crate::leanh::lean_dec(v___x_2514_);
    v___x_2516_ = l_Lean_Environment_contains(v_env_2515_, v_constName_2510_, v_skipRealize_2511_);
    v___x_2517_ = crate::leanh::lean_box((v___x_2516_) as usize);
    v___x_2518_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2518_, 0, v___x_2517_);
    return v___x_2518_;
}
pub unsafe fn l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg___boxed(
    mut v_constName_2519_: *mut crate::leanh::LeanObject,
    mut v_skipRealize_2520_: *mut crate::leanh::LeanObject,
    mut v___y_2521_: *mut crate::leanh::LeanObject,
    mut v___y_2522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipRealize_boxed_2523_: u8 = 0;
    let mut v_res_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_2523_ = (crate::leanh::lean_unbox(v_skipRealize_2520_) as u8);
    v_res_2524_ = l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg(
        v_constName_2519_,
        v_skipRealize_boxed_2523_,
        v___y_2521_,
    );
    crate::leanh::lean_dec(v___y_2521_);
    return v_res_2524_;
}
pub unsafe fn l_Lean_hasConst___at___00mkCtorIdx_spec__1(
    mut v_constName_2525_: *mut crate::leanh::LeanObject,
    mut v_skipRealize_2526_: u8,
    mut v___y_2527_: *mut crate::leanh::LeanObject,
    mut v___y_2528_: *mut crate::leanh::LeanObject,
    mut v___y_2529_: *mut crate::leanh::LeanObject,
    mut v___y_2530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2532_ = l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg(
        v_constName_2525_,
        v_skipRealize_2526_,
        v___y_2530_,
    );
    return v___x_2532_;
}
pub unsafe fn l_Lean_hasConst___at___00mkCtorIdx_spec__1___boxed(
    mut v_constName_2533_: *mut crate::leanh::LeanObject,
    mut v_skipRealize_2534_: *mut crate::leanh::LeanObject,
    mut v___y_2535_: *mut crate::leanh::LeanObject,
    mut v___y_2536_: *mut crate::leanh::LeanObject,
    mut v___y_2537_: *mut crate::leanh::LeanObject,
    mut v___y_2538_: *mut crate::leanh::LeanObject,
    mut v___y_2539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipRealize_boxed_2540_: u8 = 0;
    let mut v_res_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_2540_ = (crate::leanh::lean_unbox(v_skipRealize_2534_) as u8);
    v_res_2541_ = l_Lean_hasConst___at___00mkCtorIdx_spec__1(
        v_constName_2533_,
        v_skipRealize_boxed_2540_,
        v___y_2535_,
        v___y_2536_,
        v___y_2537_,
        v___y_2538_,
    );
    crate::leanh::lean_dec(v___y_2538_);
    crate::leanh::lean_dec_ref(v___y_2537_);
    crate::leanh::lean_dec(v___y_2536_);
    crate::leanh::lean_dec_ref(v___y_2535_);
    return v_res_2541_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0(
    mut v_k_2542_: *mut crate::leanh::LeanObject,
    mut v_b_2543_: *mut crate::leanh::LeanObject,
    mut v_c_2544_: *mut crate::leanh::LeanObject,
    mut v___y_2545_: *mut crate::leanh::LeanObject,
    mut v___y_2546_: *mut crate::leanh::LeanObject,
    mut v___y_2547_: *mut crate::leanh::LeanObject,
    mut v___y_2548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_2548_);
    crate::leanh::lean_inc_ref(v___y_2547_);
    crate::leanh::lean_inc(v___y_2546_);
    crate::leanh::lean_inc_ref(v___y_2545_);
    v___x_2550_ = crate::leanh::lean_apply_7(
        v_k_2542_,
        v_b_2543_,
        v_c_2544_,
        v___y_2545_,
        v___y_2546_,
        v___y_2547_,
        v___y_2548_,
        crate::leanh::lean_box(0),
    );
    return v___x_2550_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0___boxed(
    mut v_k_2551_: *mut crate::leanh::LeanObject,
    mut v_b_2552_: *mut crate::leanh::LeanObject,
    mut v_c_2553_: *mut crate::leanh::LeanObject,
    mut v___y_2554_: *mut crate::leanh::LeanObject,
    mut v___y_2555_: *mut crate::leanh::LeanObject,
    mut v___y_2556_: *mut crate::leanh::LeanObject,
    mut v___y_2557_: *mut crate::leanh::LeanObject,
    mut v___y_2558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2559_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0(
        v_k_2551_,
        v_b_2552_,
        v_c_2553_,
        v___y_2554_,
        v___y_2555_,
        v___y_2556_,
        v___y_2557_,
    );
    crate::leanh::lean_dec(v___y_2557_);
    crate::leanh::lean_dec_ref(v___y_2556_);
    crate::leanh::lean_dec(v___y_2555_);
    crate::leanh::lean_dec_ref(v___y_2554_);
    return v_res_2559_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg(
    mut v_type_2560_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_2561_: *mut crate::leanh::LeanObject,
    mut v_k_2562_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2563_: u8,
    mut v_whnfType_2564_: u8,
    mut v___y_2565_: *mut crate::leanh::LeanObject,
    mut v___y_2566_: *mut crate::leanh::LeanObject,
    mut v___y_2567_: *mut crate::leanh::LeanObject,
    mut v___y_2568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2575_: u8 = 0;
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2579_: u8 = 0;
    let mut v_a_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2583_: u8 = 0;
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2587_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2570_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_2570_, 0, v_k_2562_);
                v___x_2571_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    crate::leanh::lean_box(0),
                    v_type_2560_,
                    v_maxFVars_x3f_2561_,
                    v___f_2570_,
                    v_cleanupAnnotations_2563_,
                    v_whnfType_2564_,
                    v___y_2565_,
                    v___y_2566_,
                    v___y_2567_,
                    v___y_2568_,
                );
                if crate::leanh::lean_obj_tag(v___x_2571_) == 0 {
                    v_a_2572_ = crate::leanh::lean_ctor_get(v___x_2571_, 0);
                    v_isSharedCheck_2579_ = (!crate::leanh::lean_is_exclusive(v___x_2571_)) as u8;
                    if v_isSharedCheck_2579_ == 0 {
                        v___x_2574_ = v___x_2571_;
                        v_isShared_2575_ = v_isSharedCheck_2579_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2572_);
                        crate::leanh::lean_dec(v___x_2571_);
                        v___x_2574_ = crate::leanh::lean_box(0);
                        v_isShared_2575_ = v_isSharedCheck_2579_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2580_ = crate::leanh::lean_ctor_get(v___x_2571_, 0);
                    v_isSharedCheck_2587_ = (!crate::leanh::lean_is_exclusive(v___x_2571_)) as u8;
                    if v_isSharedCheck_2587_ == 0 {
                        v___x_2582_ = v___x_2571_;
                        v_isShared_2583_ = v_isSharedCheck_2587_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2580_);
                        crate::leanh::lean_dec(v___x_2571_);
                        v___x_2582_ = crate::leanh::lean_box(0);
                        v_isShared_2583_ = v_isSharedCheck_2587_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2575_ == 0 {
                    v___x_2577_ = v___x_2574_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2578_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
                    v___x_2577_ = v_reuseFailAlloc_2578_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2577_;
            }
            3 => {
                if v_isShared_2583_ == 0 {
                    v___x_2585_ = v___x_2582_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2586_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2580_);
                    v___x_2585_ = v_reuseFailAlloc_2586_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2585_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___boxed(
    mut v_type_2588_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_2589_: *mut crate::leanh::LeanObject,
    mut v_k_2590_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2591_: *mut crate::leanh::LeanObject,
    mut v_whnfType_2592_: *mut crate::leanh::LeanObject,
    mut v___y_2593_: *mut crate::leanh::LeanObject,
    mut v___y_2594_: *mut crate::leanh::LeanObject,
    mut v___y_2595_: *mut crate::leanh::LeanObject,
    mut v___y_2596_: *mut crate::leanh::LeanObject,
    mut v___y_2597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2598_: u8 = 0;
    let mut v_whnfType_boxed_2599_: u8 = 0;
    let mut v_res_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2598_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_2591_) as u8);
    v_whnfType_boxed_2599_ = (crate::leanh::lean_unbox(v_whnfType_2592_) as u8);
    v_res_2600_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg(
        v_type_2588_,
        v_maxFVars_x3f_2589_,
        v_k_2590_,
        v_cleanupAnnotations_boxed_2598_,
        v_whnfType_boxed_2599_,
        v___y_2593_,
        v___y_2594_,
        v___y_2595_,
        v___y_2596_,
    );
    crate::leanh::lean_dec(v___y_2596_);
    crate::leanh::lean_dec_ref(v___y_2595_);
    crate::leanh::lean_dec(v___y_2594_);
    crate::leanh::lean_dec_ref(v___y_2593_);
    return v_res_2600_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5(
    mut v_00_u03b1_2601_: *mut crate::leanh::LeanObject,
    mut v_type_2602_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_2603_: *mut crate::leanh::LeanObject,
    mut v_k_2604_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2605_: u8,
    mut v_whnfType_2606_: u8,
    mut v___y_2607_: *mut crate::leanh::LeanObject,
    mut v___y_2608_: *mut crate::leanh::LeanObject,
    mut v___y_2609_: *mut crate::leanh::LeanObject,
    mut v___y_2610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2612_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg(
        v_type_2602_,
        v_maxFVars_x3f_2603_,
        v_k_2604_,
        v_cleanupAnnotations_2605_,
        v_whnfType_2606_,
        v___y_2607_,
        v___y_2608_,
        v___y_2609_,
        v___y_2610_,
    );
    return v___x_2612_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___boxed(
    mut v_00_u03b1_2613_: *mut crate::leanh::LeanObject,
    mut v_type_2614_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_2615_: *mut crate::leanh::LeanObject,
    mut v_k_2616_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2617_: *mut crate::leanh::LeanObject,
    mut v_whnfType_2618_: *mut crate::leanh::LeanObject,
    mut v___y_2619_: *mut crate::leanh::LeanObject,
    mut v___y_2620_: *mut crate::leanh::LeanObject,
    mut v___y_2621_: *mut crate::leanh::LeanObject,
    mut v___y_2622_: *mut crate::leanh::LeanObject,
    mut v___y_2623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2624_: u8 = 0;
    let mut v_whnfType_boxed_2625_: u8 = 0;
    let mut v_res_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2624_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_2617_) as u8);
    v_whnfType_boxed_2625_ = (crate::leanh::lean_unbox(v_whnfType_2618_) as u8);
    v_res_2626_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5(
        v_00_u03b1_2613_,
        v_type_2614_,
        v_maxFVars_x3f_2615_,
        v_k_2616_,
        v_cleanupAnnotations_boxed_2624_,
        v_whnfType_boxed_2625_,
        v___y_2619_,
        v___y_2620_,
        v___y_2621_,
        v___y_2622_,
    );
    crate::leanh::lean_dec(v___y_2622_);
    crate::leanh::lean_dec_ref(v___y_2621_);
    crate::leanh::lean_dec(v___y_2620_);
    crate::leanh::lean_dec_ref(v___y_2619_);
    return v_res_2626_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(
    mut v_name_2627_: *mut crate::leanh::LeanObject,
    mut v_levelParams_2628_: *mut crate::leanh::LeanObject,
    mut v_type_2629_: *mut crate::leanh::LeanObject,
    mut v_value_2630_: *mut crate::leanh::LeanObject,
    mut v_hints_2631_: *mut crate::leanh::LeanObject,
    mut v___y_2632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2636_: u8 = 0;
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2643_: u8 = 0;
    let mut v___x_2644_: u8 = 0;
    let mut v___x_2645_: u8 = 0;
    let mut v_env_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: u8 = 0;
    let mut v___x_2648_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2634_ = lean_st_ref_get(v___y_2632_);
                v_env_2646_ = crate::leanh::lean_ctor_get(v___x_2634_, 0);
                crate::leanh::lean_inc_ref_n(v_env_2646_, 2);
                crate::leanh::lean_dec(v___x_2634_);
                v___x_2647_ = l_Lean_Environment_hasUnsafe(v_env_2646_, v_type_2629_);
                if v___x_2647_ == 0 {
                    v___x_2648_ = l_Lean_Environment_hasUnsafe(v_env_2646_, v_value_2630_);
                    v___y_2643_ = v___x_2648_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_env_2646_);
                    v___y_2643_ = v___x_2647_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_name_2627_);
                v___x_2637_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2637_, 0, v_name_2627_);
                crate::leanh::lean_ctor_set(v___x_2637_, 1, v_levelParams_2628_);
                crate::leanh::lean_ctor_set(v___x_2637_, 2, v_type_2629_);
                v___x_2638_ = crate::leanh::lean_box(0);
                v___x_2639_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2639_, 0, v_name_2627_);
                crate::leanh::lean_ctor_set(v___x_2639_, 1, v___x_2638_);
                v___x_2640_ = crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2640_, 0, v___x_2637_);
                crate::leanh::lean_ctor_set(v___x_2640_, 1, v_value_2630_);
                crate::leanh::lean_ctor_set(v___x_2640_, 2, v_hints_2631_);
                crate::leanh::lean_ctor_set(v___x_2640_, 3, v___x_2639_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2640_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___y_2636_,
                );
                v___x_2641_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2641_, 0, v___x_2640_);
                return v___x_2641_;
            }
            2 => {
                if v___y_2643_ == 0 {
                    v___x_2644_ = 1;
                    v___y_2636_ = v___x_2644_;
                    state = 1;
                    continue;
                } else {
                    v___x_2645_ = 0;
                    v___y_2636_ = v___x_2645_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg___boxed(
    mut v_name_2649_: *mut crate::leanh::LeanObject,
    mut v_levelParams_2650_: *mut crate::leanh::LeanObject,
    mut v_type_2651_: *mut crate::leanh::LeanObject,
    mut v_value_2652_: *mut crate::leanh::LeanObject,
    mut v_hints_2653_: *mut crate::leanh::LeanObject,
    mut v___y_2654_: *mut crate::leanh::LeanObject,
    mut v___y_2655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2656_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(
        v_name_2649_,
        v_levelParams_2650_,
        v_type_2651_,
        v_value_2652_,
        v_hints_2653_,
        v___y_2654_,
    );
    crate::leanh::lean_dec(v___y_2654_);
    return v_res_2656_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8(
    mut v_name_2657_: *mut crate::leanh::LeanObject,
    mut v_levelParams_2658_: *mut crate::leanh::LeanObject,
    mut v_type_2659_: *mut crate::leanh::LeanObject,
    mut v_value_2660_: *mut crate::leanh::LeanObject,
    mut v_hints_2661_: *mut crate::leanh::LeanObject,
    mut v___y_2662_: *mut crate::leanh::LeanObject,
    mut v___y_2663_: *mut crate::leanh::LeanObject,
    mut v___y_2664_: *mut crate::leanh::LeanObject,
    mut v___y_2665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2667_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(
        v_name_2657_,
        v_levelParams_2658_,
        v_type_2659_,
        v_value_2660_,
        v_hints_2661_,
        v___y_2665_,
    );
    return v___x_2667_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___boxed(
    mut v_name_2668_: *mut crate::leanh::LeanObject,
    mut v_levelParams_2669_: *mut crate::leanh::LeanObject,
    mut v_type_2670_: *mut crate::leanh::LeanObject,
    mut v_value_2671_: *mut crate::leanh::LeanObject,
    mut v_hints_2672_: *mut crate::leanh::LeanObject,
    mut v___y_2673_: *mut crate::leanh::LeanObject,
    mut v___y_2674_: *mut crate::leanh::LeanObject,
    mut v___y_2675_: *mut crate::leanh::LeanObject,
    mut v___y_2676_: *mut crate::leanh::LeanObject,
    mut v___y_2677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2678_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8(
        v_name_2668_,
        v_levelParams_2669_,
        v_type_2670_,
        v_value_2671_,
        v_hints_2672_,
        v___y_2673_,
        v___y_2674_,
        v___y_2675_,
        v___y_2676_,
    );
    crate::leanh::lean_dec(v___y_2676_);
    crate::leanh::lean_dec_ref(v___y_2675_);
    crate::leanh::lean_dec(v___y_2674_);
    crate::leanh::lean_dec_ref(v___y_2673_);
    return v_res_2678_;
}
pub unsafe fn l_panic___at___00mkCtorIdx_spec__13(
    mut v_msg_2680_: *mut crate::leanh::LeanObject,
    mut v___y_2681_: *mut crate::leanh::LeanObject,
    mut v___y_2682_: *mut crate::leanh::LeanObject,
    mut v___y_2683_: *mut crate::leanh::LeanObject,
    mut v___y_2684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_26648__overap_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2686_ = l_panic___at___00mkCtorIdx_spec__13___closed__0;
    v___x_26648__overap_2687_ = lean_panic_fn_borrowed(v___f_2686_, v_msg_2680_);
    crate::leanh::lean_inc(v___y_2684_);
    crate::leanh::lean_inc_ref(v___y_2683_);
    crate::leanh::lean_inc(v___y_2682_);
    crate::leanh::lean_inc_ref(v___y_2681_);
    v___x_2688_ = crate::leanh::lean_apply_5(
        v___x_26648__overap_2687_,
        v___y_2681_,
        v___y_2682_,
        v___y_2683_,
        v___y_2684_,
        crate::leanh::lean_box(0),
    );
    return v___x_2688_;
}
pub unsafe fn l_panic___at___00mkCtorIdx_spec__13___boxed(
    mut v_msg_2689_: *mut crate::leanh::LeanObject,
    mut v___y_2690_: *mut crate::leanh::LeanObject,
    mut v___y_2691_: *mut crate::leanh::LeanObject,
    mut v___y_2692_: *mut crate::leanh::LeanObject,
    mut v___y_2693_: *mut crate::leanh::LeanObject,
    mut v___y_2694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2695_ = l_panic___at___00mkCtorIdx_spec__13(
        v_msg_2689_,
        v___y_2690_,
        v___y_2691_,
        v___y_2692_,
        v___y_2693_,
    );
    crate::leanh::lean_dec(v___y_2693_);
    crate::leanh::lean_dec_ref(v___y_2692_);
    crate::leanh::lean_dec(v___y_2691_);
    crate::leanh::lean_dec_ref(v___y_2690_);
    return v_res_2695_;
}
pub unsafe fn l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0(
    mut v___y_2696_: *mut crate::leanh::LeanObject,
    mut v_isExporting_2697_: u8,
    mut v___x_2698_: *mut crate::leanh::LeanObject,
    mut v___y_2699_: *mut crate::leanh::LeanObject,
    mut v___x_2700_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_2701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2714_: u8 = 0;
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2726_: u8 = 0;
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2733_: u8 = 0;
    let mut v_unused_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2736_: u8 = 0;
    let mut v_unused_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2703_ = lean_st_ref_take(v___y_2696_);
                v_env_2704_ = crate::leanh::lean_ctor_get(v___x_2703_, 0);
                v_nextMacroScope_2705_ = crate::leanh::lean_ctor_get(v___x_2703_, 1);
                v_ngen_2706_ = crate::leanh::lean_ctor_get(v___x_2703_, 2);
                v_auxDeclNGen_2707_ = crate::leanh::lean_ctor_get(v___x_2703_, 3);
                v_traceState_2708_ = crate::leanh::lean_ctor_get(v___x_2703_, 4);
                v_messages_2709_ = crate::leanh::lean_ctor_get(v___x_2703_, 6);
                v_infoState_2710_ = crate::leanh::lean_ctor_get(v___x_2703_, 7);
                v_snapshotTasks_2711_ = crate::leanh::lean_ctor_get(v___x_2703_, 8);
                v_isSharedCheck_2736_ = (!crate::leanh::lean_is_exclusive(v___x_2703_)) as u8;
                if v_isSharedCheck_2736_ == 0 {
                    v_unused_2737_ = crate::leanh::lean_ctor_get(v___x_2703_, 5);
                    crate::leanh::lean_dec(v_unused_2737_);
                    v___x_2713_ = v___x_2703_;
                    v_isShared_2714_ = v_isSharedCheck_2736_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2711_);
                    crate::leanh::lean_inc(v_infoState_2710_);
                    crate::leanh::lean_inc(v_messages_2709_);
                    crate::leanh::lean_inc(v_traceState_2708_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2707_);
                    crate::leanh::lean_inc(v_ngen_2706_);
                    crate::leanh::lean_inc(v_nextMacroScope_2705_);
                    crate::leanh::lean_inc(v_env_2704_);
                    crate::leanh::lean_dec(v___x_2703_);
                    v___x_2713_ = crate::leanh::lean_box(0);
                    v_isShared_2714_ = v_isSharedCheck_2736_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2715_ = l_Lean_Environment_setExporting(v_env_2704_, v_isExporting_2697_);
                if v_isShared_2714_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2713_, 5, v___x_2698_);
                    crate::leanh::lean_ctor_set(v___x_2713_, 0, v___x_2715_);
                    v___x_2717_ = v___x_2713_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2735_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2715_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 1, v_nextMacroScope_2705_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 2, v_ngen_2706_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 3, v_auxDeclNGen_2707_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 4, v_traceState_2708_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 5, v___x_2698_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 6, v_messages_2709_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 7, v_infoState_2710_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 8, v_snapshotTasks_2711_);
                    v___x_2717_ = v_reuseFailAlloc_2735_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2718_ = lean_st_ref_set(v___y_2696_, v___x_2717_);
                v___x_2719_ = lean_st_ref_take(v___y_2699_);
                v_mctx_2720_ = crate::leanh::lean_ctor_get(v___x_2719_, 0);
                v_zetaDeltaFVarIds_2721_ = crate::leanh::lean_ctor_get(v___x_2719_, 2);
                v_postponed_2722_ = crate::leanh::lean_ctor_get(v___x_2719_, 3);
                v_diag_2723_ = crate::leanh::lean_ctor_get(v___x_2719_, 4);
                v_isSharedCheck_2733_ = (!crate::leanh::lean_is_exclusive(v___x_2719_)) as u8;
                if v_isSharedCheck_2733_ == 0 {
                    v_unused_2734_ = crate::leanh::lean_ctor_get(v___x_2719_, 1);
                    crate::leanh::lean_dec(v_unused_2734_);
                    v___x_2725_ = v___x_2719_;
                    v_isShared_2726_ = v_isSharedCheck_2733_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_2723_);
                    crate::leanh::lean_inc(v_postponed_2722_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_2721_);
                    crate::leanh::lean_inc(v_mctx_2720_);
                    crate::leanh::lean_dec(v___x_2719_);
                    v___x_2725_ = crate::leanh::lean_box(0);
                    v_isShared_2726_ = v_isSharedCheck_2733_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2726_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2725_, 1, v___x_2700_);
                    v___x_2728_ = v___x_2725_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2732_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_mctx_2720_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2732_, 1, v___x_2700_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2732_,
                        2,
                        v_zetaDeltaFVarIds_2721_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2732_, 3, v_postponed_2722_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2732_, 4, v_diag_2723_);
                    v___x_2728_ = v_reuseFailAlloc_2732_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2729_ = lean_st_ref_set(v___y_2699_, v___x_2728_);
                v___x_2730_ = crate::leanh::lean_box(0);
                v___x_2731_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2731_, 0, v___x_2730_);
                return v___x_2731_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0___boxed(
    mut v___y_2738_: *mut crate::leanh::LeanObject,
    mut v_isExporting_2739_: *mut crate::leanh::LeanObject,
    mut v___x_2740_: *mut crate::leanh::LeanObject,
    mut v___y_2741_: *mut crate::leanh::LeanObject,
    mut v___x_2742_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_2743_: *mut crate::leanh::LeanObject,
    mut v___y_2744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_2745_: u8 = 0;
    let mut v_res_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_2745_ = (crate::leanh::lean_unbox(v_isExporting_2739_) as u8);
    v_res_2746_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0(
        v___y_2738_,
        v_isExporting_boxed_2745_,
        v___x_2740_,
        v___y_2741_,
        v___x_2742_,
        v_a_x3f_2743_,
    );
    crate::leanh::lean_dec(v_a_x3f_2743_);
    crate::leanh::lean_dec(v___y_2741_);
    crate::leanh::lean_dec(v___y_2738_);
    return v_res_2746_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2747_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2747_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2748_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0_once
        ),
        _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0,
    );
    v___x_2749_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2749_, 0, v___x_2748_);
    return v___x_2749_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2750_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1_once
        ),
        _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1,
    );
    v___x_2751_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2751_, 0, v___x_2750_);
    crate::leanh::lean_ctor_set(v___x_2751_, 1, v___x_2750_);
    return v___x_2751_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2752_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1_once
        ),
        _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1,
    );
    v___x_2753_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2753_, 0, v___x_2752_);
    crate::leanh::lean_ctor_set(v___x_2753_, 1, v___x_2752_);
    crate::leanh::lean_ctor_set(v___x_2753_, 2, v___x_2752_);
    crate::leanh::lean_ctor_set(v___x_2753_, 3, v___x_2752_);
    crate::leanh::lean_ctor_set(v___x_2753_, 4, v___x_2752_);
    crate::leanh::lean_ctor_set(v___x_2753_, 5, v___x_2752_);
    return v___x_2753_;
}
pub unsafe fn l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(
    mut v_x_2754_: *mut crate::leanh::LeanObject,
    mut v_isExporting_2755_: u8,
    mut v___y_2756_: *mut crate::leanh::LeanObject,
    mut v___y_2757_: *mut crate::leanh::LeanObject,
    mut v___y_2758_: *mut crate::leanh::LeanObject,
    mut v___y_2759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_2763_: u8 = 0;
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2775_: u8 = 0;
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2788_: u8 = 0;
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2797_: u8 = 0;
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2803_: u8 = 0;
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2807_: u8 = 0;
    let mut v_unused_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2810_: u8 = 0;
    let mut v_a_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2816_: u8 = 0;
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2820_: u8 = 0;
    let mut v_unused_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2823_: u8 = 0;
    let mut v_unused_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2826_: u8 = 0;
    let mut v_unused_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2761_ = lean_st_ref_get(v___y_2759_);
                v_env_2762_ = crate::leanh::lean_ctor_get(v___x_2761_, 0);
                crate::leanh::lean_inc_ref(v_env_2762_);
                crate::leanh::lean_dec(v___x_2761_);
                v_isExporting_2763_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_2762_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                crate::leanh::lean_dec_ref(v_env_2762_);
                v___x_2764_ = lean_st_ref_take(v___y_2759_);
                v_env_2765_ = crate::leanh::lean_ctor_get(v___x_2764_, 0);
                v_nextMacroScope_2766_ = crate::leanh::lean_ctor_get(v___x_2764_, 1);
                v_ngen_2767_ = crate::leanh::lean_ctor_get(v___x_2764_, 2);
                v_auxDeclNGen_2768_ = crate::leanh::lean_ctor_get(v___x_2764_, 3);
                v_traceState_2769_ = crate::leanh::lean_ctor_get(v___x_2764_, 4);
                v_messages_2770_ = crate::leanh::lean_ctor_get(v___x_2764_, 6);
                v_infoState_2771_ = crate::leanh::lean_ctor_get(v___x_2764_, 7);
                v_snapshotTasks_2772_ = crate::leanh::lean_ctor_get(v___x_2764_, 8);
                v_isSharedCheck_2826_ = (!crate::leanh::lean_is_exclusive(v___x_2764_)) as u8;
                if v_isSharedCheck_2826_ == 0 {
                    v_unused_2827_ = crate::leanh::lean_ctor_get(v___x_2764_, 5);
                    crate::leanh::lean_dec(v_unused_2827_);
                    v___x_2774_ = v___x_2764_;
                    v_isShared_2775_ = v_isSharedCheck_2826_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2772_);
                    crate::leanh::lean_inc(v_infoState_2771_);
                    crate::leanh::lean_inc(v_messages_2770_);
                    crate::leanh::lean_inc(v_traceState_2769_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2768_);
                    crate::leanh::lean_inc(v_ngen_2767_);
                    crate::leanh::lean_inc(v_nextMacroScope_2766_);
                    crate::leanh::lean_inc(v_env_2765_);
                    crate::leanh::lean_dec(v___x_2764_);
                    v___x_2774_ = crate::leanh::lean_box(0);
                    v_isShared_2775_ = v_isSharedCheck_2826_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2776_ = l_Lean_Environment_setExporting(v_env_2765_, v_isExporting_2755_);
                v___x_2777_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once
                    ),
                    _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2,
                );
                if v_isShared_2775_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2774_, 5, v___x_2777_);
                    crate::leanh::lean_ctor_set(v___x_2774_, 0, v___x_2776_);
                    v___x_2779_ = v___x_2774_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2825_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2825_, 0, v___x_2776_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2825_, 1, v_nextMacroScope_2766_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2825_, 2, v_ngen_2767_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2825_, 3, v_auxDeclNGen_2768_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2825_, 4, v_traceState_2769_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2825_, 5, v___x_2777_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2825_, 6, v_messages_2770_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2825_, 7, v_infoState_2771_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2825_, 8, v_snapshotTasks_2772_);
                    v___x_2779_ = v_reuseFailAlloc_2825_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2780_ = lean_st_ref_set(v___y_2759_, v___x_2779_);
                v___x_2781_ = lean_st_ref_take(v___y_2757_);
                v_mctx_2782_ = crate::leanh::lean_ctor_get(v___x_2781_, 0);
                v_zetaDeltaFVarIds_2783_ = crate::leanh::lean_ctor_get(v___x_2781_, 2);
                v_postponed_2784_ = crate::leanh::lean_ctor_get(v___x_2781_, 3);
                v_diag_2785_ = crate::leanh::lean_ctor_get(v___x_2781_, 4);
                v_isSharedCheck_2823_ = (!crate::leanh::lean_is_exclusive(v___x_2781_)) as u8;
                if v_isSharedCheck_2823_ == 0 {
                    v_unused_2824_ = crate::leanh::lean_ctor_get(v___x_2781_, 1);
                    crate::leanh::lean_dec(v_unused_2824_);
                    v___x_2787_ = v___x_2781_;
                    v_isShared_2788_ = v_isSharedCheck_2823_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_2785_);
                    crate::leanh::lean_inc(v_postponed_2784_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_2783_);
                    crate::leanh::lean_inc(v_mctx_2782_);
                    crate::leanh::lean_dec(v___x_2781_);
                    v___x_2787_ = crate::leanh::lean_box(0);
                    v_isShared_2788_ = v_isSharedCheck_2823_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2789_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once
                    ),
                    _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3,
                );
                if v_isShared_2788_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2787_, 1, v___x_2789_);
                    v___x_2791_ = v___x_2787_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2822_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_mctx_2782_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 1, v___x_2789_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2822_,
                        2,
                        v_zetaDeltaFVarIds_2783_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 3, v_postponed_2784_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 4, v_diag_2785_);
                    v___x_2791_ = v_reuseFailAlloc_2822_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2792_ = lean_st_ref_set(v___y_2757_, v___x_2791_);
                crate::leanh::lean_inc(v___y_2759_);
                crate::leanh::lean_inc_ref(v___y_2758_);
                crate::leanh::lean_inc(v___y_2757_);
                crate::leanh::lean_inc_ref(v___y_2756_);
                v_r_2793_ = crate::leanh::lean_apply_5(
                    v_x_2754_,
                    v___y_2756_,
                    v___y_2757_,
                    v___y_2758_,
                    v___y_2759_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v_r_2793_) == 0 {
                    v_a_2794_ = crate::leanh::lean_ctor_get(v_r_2793_, 0);
                    v_isSharedCheck_2810_ = (!crate::leanh::lean_is_exclusive(v_r_2793_)) as u8;
                    if v_isSharedCheck_2810_ == 0 {
                        v___x_2796_ = v_r_2793_;
                        v_isShared_2797_ = v_isSharedCheck_2810_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2794_);
                        crate::leanh::lean_dec(v_r_2793_);
                        v___x_2796_ = crate::leanh::lean_box(0);
                        v_isShared_2797_ = v_isSharedCheck_2810_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_2811_ = crate::leanh::lean_ctor_get(v_r_2793_, 0);
                    crate::leanh::lean_inc(v_a_2811_);
                    crate::leanh::lean_dec_ref_known(v_r_2793_, 1);
                    v___x_2812_ = crate::leanh::lean_box(0);
                    v___x_2813_ =
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0(
                            v___y_2759_,
                            v_isExporting_2763_,
                            v___x_2777_,
                            v___y_2757_,
                            v___x_2789_,
                            v___x_2812_,
                        );
                    v_isSharedCheck_2820_ = (!crate::leanh::lean_is_exclusive(v___x_2813_)) as u8;
                    if v_isSharedCheck_2820_ == 0 {
                        v_unused_2821_ = crate::leanh::lean_ctor_get(v___x_2813_, 0);
                        crate::leanh::lean_dec(v_unused_2821_);
                        v___x_2815_ = v___x_2813_;
                        v_isShared_2816_ = v_isSharedCheck_2820_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2813_);
                        v___x_2815_ = crate::leanh::lean_box(0);
                        v_isShared_2816_ = v_isSharedCheck_2820_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                crate::leanh::lean_inc(v_a_2794_);
                if v_isShared_2797_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2796_, 1);
                    v___x_2799_ = v___x_2796_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2809_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_a_2794_);
                    v___x_2799_ = v_reuseFailAlloc_2809_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2800_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0(
                    v___y_2759_,
                    v_isExporting_2763_,
                    v___x_2777_,
                    v___y_2757_,
                    v___x_2789_,
                    v___x_2799_,
                );
                crate::leanh::lean_dec_ref(v___x_2799_);
                v_isSharedCheck_2807_ = (!crate::leanh::lean_is_exclusive(v___x_2800_)) as u8;
                if v_isSharedCheck_2807_ == 0 {
                    v_unused_2808_ = crate::leanh::lean_ctor_get(v___x_2800_, 0);
                    crate::leanh::lean_dec(v_unused_2808_);
                    v___x_2802_ = v___x_2800_;
                    v_isShared_2803_ = v_isSharedCheck_2807_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2800_);
                    v___x_2802_ = crate::leanh::lean_box(0);
                    v_isShared_2803_ = v_isSharedCheck_2807_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2803_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2802_, 0, v_a_2794_);
                    v___x_2805_ = v___x_2802_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2806_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2794_);
                    v___x_2805_ = v_reuseFailAlloc_2806_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2805_;
            }
            9 => {
                if v_isShared_2816_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2815_, 1);
                    crate::leanh::lean_ctor_set(v___x_2815_, 0, v_a_2811_);
                    v___x_2818_ = v___x_2815_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2819_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2811_);
                    v___x_2818_ = v_reuseFailAlloc_2819_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2818_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___boxed(
    mut v_x_2828_: *mut crate::leanh::LeanObject,
    mut v_isExporting_2829_: *mut crate::leanh::LeanObject,
    mut v___y_2830_: *mut crate::leanh::LeanObject,
    mut v___y_2831_: *mut crate::leanh::LeanObject,
    mut v___y_2832_: *mut crate::leanh::LeanObject,
    mut v___y_2833_: *mut crate::leanh::LeanObject,
    mut v___y_2834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_2835_: u8 = 0;
    let mut v_res_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_2835_ = (crate::leanh::lean_unbox(v_isExporting_2829_) as u8);
    v_res_2836_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(
        v_x_2828_,
        v_isExporting_boxed_2835_,
        v___y_2830_,
        v___y_2831_,
        v___y_2832_,
        v___y_2833_,
    );
    crate::leanh::lean_dec(v___y_2833_);
    crate::leanh::lean_dec_ref(v___y_2832_);
    crate::leanh::lean_dec(v___y_2831_);
    crate::leanh::lean_dec_ref(v___y_2830_);
    return v_res_2836_;
}
pub unsafe fn l_Lean_withExporting___at___00mkCtorIdx_spec__14(
    mut v_00_u03b1_2837_: *mut crate::leanh::LeanObject,
    mut v_x_2838_: *mut crate::leanh::LeanObject,
    mut v_isExporting_2839_: u8,
    mut v___y_2840_: *mut crate::leanh::LeanObject,
    mut v___y_2841_: *mut crate::leanh::LeanObject,
    mut v___y_2842_: *mut crate::leanh::LeanObject,
    mut v___y_2843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2845_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(
        v_x_2838_,
        v_isExporting_2839_,
        v___y_2840_,
        v___y_2841_,
        v___y_2842_,
        v___y_2843_,
    );
    return v___x_2845_;
}
pub unsafe fn l_Lean_withExporting___at___00mkCtorIdx_spec__14___boxed(
    mut v_00_u03b1_2846_: *mut crate::leanh::LeanObject,
    mut v_x_2847_: *mut crate::leanh::LeanObject,
    mut v_isExporting_2848_: *mut crate::leanh::LeanObject,
    mut v___y_2849_: *mut crate::leanh::LeanObject,
    mut v___y_2850_: *mut crate::leanh::LeanObject,
    mut v___y_2851_: *mut crate::leanh::LeanObject,
    mut v___y_2852_: *mut crate::leanh::LeanObject,
    mut v___y_2853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_2854_: u8 = 0;
    let mut v_res_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_2854_ = (crate::leanh::lean_unbox(v_isExporting_2848_) as u8);
    v_res_2855_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14(
        v_00_u03b1_2846_,
        v_x_2847_,
        v_isExporting_boxed_2854_,
        v___y_2849_,
        v___y_2850_,
        v___y_2851_,
        v___y_2852_,
    );
    crate::leanh::lean_dec(v___y_2852_);
    crate::leanh::lean_dec_ref(v___y_2851_);
    crate::leanh::lean_dec(v___y_2850_);
    crate::leanh::lean_dec_ref(v___y_2849_);
    return v_res_2855_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5_spec__11(
    mut v_msgData_2856_: *mut crate::leanh::LeanObject,
    mut v___y_2857_: *mut crate::leanh::LeanObject,
    mut v___y_2858_: *mut crate::leanh::LeanObject,
    mut v___y_2859_: *mut crate::leanh::LeanObject,
    mut v___y_2860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2862_ = lean_st_ref_get(v___y_2860_);
    v_env_2863_ = crate::leanh::lean_ctor_get(v___x_2862_, 0);
    crate::leanh::lean_inc_ref(v_env_2863_);
    crate::leanh::lean_dec(v___x_2862_);
    v___x_2864_ = lean_st_ref_get(v___y_2858_);
    v_mctx_2865_ = crate::leanh::lean_ctor_get(v___x_2864_, 0);
    crate::leanh::lean_inc_ref(v_mctx_2865_);
    crate::leanh::lean_dec(v___x_2864_);
    v_lctx_2866_ = crate::leanh::lean_ctor_get(v___y_2857_, 2);
    v_options_2867_ = crate::leanh::lean_ctor_get(v___y_2859_, 2);
    crate::leanh::lean_inc_ref(v_options_2867_);
    crate::leanh::lean_inc_ref(v_lctx_2866_);
    v___x_2868_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2868_, 0, v_env_2863_);
    crate::leanh::lean_ctor_set(v___x_2868_, 1, v_mctx_2865_);
    crate::leanh::lean_ctor_set(v___x_2868_, 2, v_lctx_2866_);
    crate::leanh::lean_ctor_set(v___x_2868_, 3, v_options_2867_);
    v___x_2869_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2869_, 0, v___x_2868_);
    crate::leanh::lean_ctor_set(v___x_2869_, 1, v_msgData_2856_);
    v___x_2870_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2870_, 0, v___x_2869_);
    return v___x_2870_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5_spec__11___boxed(
    mut v_msgData_2871_: *mut crate::leanh::LeanObject,
    mut v___y_2872_: *mut crate::leanh::LeanObject,
    mut v___y_2873_: *mut crate::leanh::LeanObject,
    mut v___y_2874_: *mut crate::leanh::LeanObject,
    mut v___y_2875_: *mut crate::leanh::LeanObject,
    mut v___y_2876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2877_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5_spec__11(v_msgData_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
    crate::leanh::lean_dec(v___y_2875_);
    crate::leanh::lean_dec_ref(v___y_2874_);
    crate::leanh::lean_dec(v___y_2873_);
    crate::leanh::lean_dec_ref(v___y_2872_);
    return v_res_2877_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(
    mut v_msg_2878_: *mut crate::leanh::LeanObject,
    mut v___y_2879_: *mut crate::leanh::LeanObject,
    mut v___y_2880_: *mut crate::leanh::LeanObject,
    mut v___y_2881_: *mut crate::leanh::LeanObject,
    mut v___y_2882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2889_: u8 = 0;
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2894_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2884_ = crate::leanh::lean_ctor_get(v___y_2881_, 5);
                v___x_2885_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5_spec__11(v_msg_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
                v_a_2886_ = crate::leanh::lean_ctor_get(v___x_2885_, 0);
                v_isSharedCheck_2894_ = (!crate::leanh::lean_is_exclusive(v___x_2885_)) as u8;
                if v_isSharedCheck_2894_ == 0 {
                    v___x_2888_ = v___x_2885_;
                    v_isShared_2889_ = v_isSharedCheck_2894_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2886_);
                    crate::leanh::lean_dec(v___x_2885_);
                    v___x_2888_ = crate::leanh::lean_box(0);
                    v_isShared_2889_ = v_isSharedCheck_2894_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_2884_);
                v___x_2890_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2890_, 0, v_ref_2884_);
                crate::leanh::lean_ctor_set(v___x_2890_, 1, v_a_2886_);
                if v_isShared_2889_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2888_, 1);
                    crate::leanh::lean_ctor_set(v___x_2888_, 0, v___x_2890_);
                    v___x_2892_ = v___x_2888_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2893_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2893_, 0, v___x_2890_);
                    v___x_2892_ = v_reuseFailAlloc_2893_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2892_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg___boxed(
    mut v_msg_2895_: *mut crate::leanh::LeanObject,
    mut v___y_2896_: *mut crate::leanh::LeanObject,
    mut v___y_2897_: *mut crate::leanh::LeanObject,
    mut v___y_2898_: *mut crate::leanh::LeanObject,
    mut v___y_2899_: *mut crate::leanh::LeanObject,
    mut v___y_2900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2901_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v_msg_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
    crate::leanh::lean_dec(v___y_2899_);
    crate::leanh::lean_dec_ref(v___y_2898_);
    crate::leanh::lean_dec(v___y_2897_);
    crate::leanh::lean_dec_ref(v___y_2896_);
    return v_res_2901_;
}
pub unsafe fn _init_l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2902_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_2902_;
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6(
    mut v_msg_2907_: *mut crate::leanh::LeanObject,
    mut v___y_2908_: *mut crate::leanh::LeanObject,
    mut v___y_2909_: *mut crate::leanh::LeanObject,
    mut v___y_2910_: *mut crate::leanh::LeanObject,
    mut v___y_2911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2918_: u8 = 0;
    let mut v_toFunctor_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2925_: u8 = 0;
    let mut v___f_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2942_: u8 = 0;
    let mut v_toFunctor_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2949_: u8 = 0;
    let mut v___f_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_30010__overap_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2968_: u8 = 0;
    let mut v_unused_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2970_: u8 = 0;
    let mut v_unused_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2974_: u8 = 0;
    let mut v_unused_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2976_: u8 = 0;
    let mut v_unused_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2913_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0_once), _init_l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0);
                v___x_2914_ = l_StateRefT_x27_instMonad___redArg(v___x_2913_);
                v_toApplicative_2915_ = crate::leanh::lean_ctor_get(v___x_2914_, 0);
                v_isSharedCheck_2976_ = (!crate::leanh::lean_is_exclusive(v___x_2914_)) as u8;
                if v_isSharedCheck_2976_ == 0 {
                    v_unused_2977_ = crate::leanh::lean_ctor_get(v___x_2914_, 1);
                    crate::leanh::lean_dec(v_unused_2977_);
                    v___x_2917_ = v___x_2914_;
                    v_isShared_2918_ = v_isSharedCheck_2976_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_2915_);
                    crate::leanh::lean_dec(v___x_2914_);
                    v___x_2917_ = crate::leanh::lean_box(0);
                    v_isShared_2918_ = v_isSharedCheck_2976_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2919_ = crate::leanh::lean_ctor_get(v_toApplicative_2915_, 0);
                v_toSeq_2920_ = crate::leanh::lean_ctor_get(v_toApplicative_2915_, 2);
                v_toSeqLeft_2921_ = crate::leanh::lean_ctor_get(v_toApplicative_2915_, 3);
                v_toSeqRight_2922_ = crate::leanh::lean_ctor_get(v_toApplicative_2915_, 4);
                v_isSharedCheck_2974_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_2915_)) as u8;
                if v_isSharedCheck_2974_ == 0 {
                    v_unused_2975_ = crate::leanh::lean_ctor_get(v_toApplicative_2915_, 1);
                    crate::leanh::lean_dec(v_unused_2975_);
                    v___x_2924_ = v_toApplicative_2915_;
                    v_isShared_2925_ = v_isSharedCheck_2974_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_2922_);
                    crate::leanh::lean_inc(v_toSeqLeft_2921_);
                    crate::leanh::lean_inc(v_toSeq_2920_);
                    crate::leanh::lean_inc(v_toFunctor_2919_);
                    crate::leanh::lean_dec(v_toApplicative_2915_);
                    v___x_2924_ = crate::leanh::lean_box(0);
                    v_isShared_2925_ = v_isSharedCheck_2974_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2926_ = l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__1;
                v___f_2927_ = l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_2919_);
                v___f_2928_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2928_, 0, v_toFunctor_2919_);
                v___f_2929_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2929_, 0, v_toFunctor_2919_);
                v___x_2930_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2930_, 0, v___f_2928_);
                crate::leanh::lean_ctor_set(v___x_2930_, 1, v___f_2929_);
                v___f_2931_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2931_, 0, v_toSeqRight_2922_);
                v___f_2932_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2932_, 0, v_toSeqLeft_2921_);
                v___f_2933_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2933_, 0, v_toSeq_2920_);
                if v_isShared_2925_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2924_, 4, v___f_2931_);
                    crate::leanh::lean_ctor_set(v___x_2924_, 3, v___f_2932_);
                    crate::leanh::lean_ctor_set(v___x_2924_, 2, v___f_2933_);
                    crate::leanh::lean_ctor_set(v___x_2924_, 1, v___f_2926_);
                    crate::leanh::lean_ctor_set(v___x_2924_, 0, v___x_2930_);
                    v___x_2935_ = v___x_2924_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2973_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2930_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 1, v___f_2926_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 2, v___f_2933_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 3, v___f_2932_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 4, v___f_2931_);
                    v___x_2935_ = v_reuseFailAlloc_2973_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2918_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2917_, 1, v___f_2927_);
                    crate::leanh::lean_ctor_set(v___x_2917_, 0, v___x_2935_);
                    v___x_2937_ = v___x_2917_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2972_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2972_, 0, v___x_2935_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2972_, 1, v___f_2927_);
                    v___x_2937_ = v_reuseFailAlloc_2972_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2938_ = l_StateRefT_x27_instMonad___redArg(v___x_2937_);
                v_toApplicative_2939_ = crate::leanh::lean_ctor_get(v___x_2938_, 0);
                v_isSharedCheck_2970_ = (!crate::leanh::lean_is_exclusive(v___x_2938_)) as u8;
                if v_isSharedCheck_2970_ == 0 {
                    v_unused_2971_ = crate::leanh::lean_ctor_get(v___x_2938_, 1);
                    crate::leanh::lean_dec(v_unused_2971_);
                    v___x_2941_ = v___x_2938_;
                    v_isShared_2942_ = v_isSharedCheck_2970_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_2939_);
                    crate::leanh::lean_dec(v___x_2938_);
                    v___x_2941_ = crate::leanh::lean_box(0);
                    v_isShared_2942_ = v_isSharedCheck_2970_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_2943_ = crate::leanh::lean_ctor_get(v_toApplicative_2939_, 0);
                v_toSeq_2944_ = crate::leanh::lean_ctor_get(v_toApplicative_2939_, 2);
                v_toSeqLeft_2945_ = crate::leanh::lean_ctor_get(v_toApplicative_2939_, 3);
                v_toSeqRight_2946_ = crate::leanh::lean_ctor_get(v_toApplicative_2939_, 4);
                v_isSharedCheck_2968_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_2939_)) as u8;
                if v_isSharedCheck_2968_ == 0 {
                    v_unused_2969_ = crate::leanh::lean_ctor_get(v_toApplicative_2939_, 1);
                    crate::leanh::lean_dec(v_unused_2969_);
                    v___x_2948_ = v_toApplicative_2939_;
                    v_isShared_2949_ = v_isSharedCheck_2968_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_2946_);
                    crate::leanh::lean_inc(v_toSeqLeft_2945_);
                    crate::leanh::lean_inc(v_toSeq_2944_);
                    crate::leanh::lean_inc(v_toFunctor_2943_);
                    crate::leanh::lean_dec(v_toApplicative_2939_);
                    v___x_2948_ = crate::leanh::lean_box(0);
                    v_isShared_2949_ = v_isSharedCheck_2968_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_2950_ = l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__3;
                v___f_2951_ = l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_2943_);
                v___f_2952_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2952_, 0, v_toFunctor_2943_);
                v___f_2953_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2953_, 0, v_toFunctor_2943_);
                v___x_2954_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2954_, 0, v___f_2952_);
                crate::leanh::lean_ctor_set(v___x_2954_, 1, v___f_2953_);
                v___f_2955_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2955_, 0, v_toSeqRight_2946_);
                v___f_2956_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2956_, 0, v_toSeqLeft_2945_);
                v___f_2957_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2957_, 0, v_toSeq_2944_);
                if v_isShared_2949_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2948_, 4, v___f_2955_);
                    crate::leanh::lean_ctor_set(v___x_2948_, 3, v___f_2956_);
                    crate::leanh::lean_ctor_set(v___x_2948_, 2, v___f_2957_);
                    crate::leanh::lean_ctor_set(v___x_2948_, 1, v___f_2950_);
                    crate::leanh::lean_ctor_set(v___x_2948_, 0, v___x_2954_);
                    v___x_2959_ = v___x_2948_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2967_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2954_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2967_, 1, v___f_2950_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2967_, 2, v___f_2957_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2967_, 3, v___f_2956_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2967_, 4, v___f_2955_);
                    v___x_2959_ = v_reuseFailAlloc_2967_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2942_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2941_, 1, v___f_2951_);
                    crate::leanh::lean_ctor_set(v___x_2941_, 0, v___x_2959_);
                    v___x_2961_ = v___x_2941_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2966_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2966_, 0, v___x_2959_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2966_, 1, v___f_2951_);
                    v___x_2961_ = v_reuseFailAlloc_2966_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2962_ = crate::leanh::lean_box(0);
                v___x_2963_ = l_instInhabitedOfMonad___redArg(v___x_2961_, v___x_2962_);
                v___x_30010__overap_2964_ = lean_panic_fn_borrowed(v___x_2963_, v_msg_2907_);
                crate::leanh::lean_dec(v___x_2963_);
                crate::leanh::lean_inc(v___y_2911_);
                crate::leanh::lean_inc_ref(v___y_2910_);
                crate::leanh::lean_inc(v___y_2909_);
                crate::leanh::lean_inc_ref(v___y_2908_);
                v___x_2965_ = crate::leanh::lean_apply_5(
                    v___x_30010__overap_2964_,
                    v___y_2908_,
                    v___y_2909_,
                    v___y_2910_,
                    v___y_2911_,
                    crate::leanh::lean_box(0),
                );
                return v___x_2965_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___boxed(
    mut v_msg_2978_: *mut crate::leanh::LeanObject,
    mut v___y_2979_: *mut crate::leanh::LeanObject,
    mut v___y_2980_: *mut crate::leanh::LeanObject,
    mut v___y_2981_: *mut crate::leanh::LeanObject,
    mut v___y_2982_: *mut crate::leanh::LeanObject,
    mut v___y_2983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2984_ = l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6(
        v_msg_2978_,
        v___y_2979_,
        v___y_2980_,
        v___y_2981_,
        v___y_2982_,
    );
    crate::leanh::lean_dec(v___y_2982_);
    crate::leanh::lean_dec_ref(v___y_2981_);
    crate::leanh::lean_dec(v___y_2980_);
    crate::leanh::lean_dec_ref(v___y_2979_);
    return v_res_2984_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2986_ = l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__0;
    v___x_2987_ = l_Lean_stringToMessageData(v___x_2986_);
    return v___x_2987_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2989_ = l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__2;
    v___x_2990_ = l_Lean_stringToMessageData(v___x_2989_);
    return v___x_2990_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2994_ = l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__6;
    v___x_2995_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_2996_ = crate::leanh::lean_unsigned_to_nat(122);
    v___x_2997_ = l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__5;
    v___x_2998_ = l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__4;
    v___x_2999_ = l_mkPanicMessageWithDecl(
        v___x_2998_,
        v___x_2997_,
        v___x_2996_,
        v___x_2995_,
        v___x_2994_,
    );
    return v___x_2999_;
}
pub unsafe fn l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4(
    mut v_constName_3000_: *mut crate::leanh::LeanObject,
    mut v___y_3001_: *mut crate::leanh::LeanObject,
    mut v___y_3002_: *mut crate::leanh::LeanObject,
    mut v___y_3003_: *mut crate::leanh::LeanObject,
    mut v___y_3004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: u8 = 0;
    let mut v___x_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: u8 = 0;
    let mut v___x_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3019_: u8 = 0;
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3024_: u8 = 0;
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3028_: u8 = 0;
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3034_: u8 = 0;
    let mut v_val_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3039_: u8 = 0;
    let mut v_a_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3043_: u8 = 0;
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3047_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3014_ = lean_st_ref_get(v___y_3004_);
                v_env_3015_ = crate::leanh::lean_ctor_get(v___x_3014_, 0);
                crate::leanh::lean_inc_ref(v_env_3015_);
                crate::leanh::lean_dec(v___x_3014_);
                v___x_3016_ = 0;
                crate::leanh::lean_inc(v_constName_3000_);
                v___x_3017_ =
                    l_Lean_Environment_findAsync_x3f(v_env_3015_, v_constName_3000_, v___x_3016_);
                if crate::leanh::lean_obj_tag(v___x_3017_) == 1 {
                    v_val_3018_ = crate::leanh::lean_ctor_get(v___x_3017_, 0);
                    crate::leanh::lean_inc(v_val_3018_);
                    crate::leanh::lean_dec_ref_known(v___x_3017_, 1);
                    v_kind_3019_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_3018_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    if v_kind_3019_ == 6 {
                        v___x_3020_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_3018_);
                        if crate::leanh::lean_obj_tag(v___x_3020_) == 6 {
                            crate::leanh::lean_dec(v_constName_3000_);
                            v_val_3021_ = crate::leanh::lean_ctor_get(v___x_3020_, 0);
                            v_isSharedCheck_3028_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3020_)) as u8;
                            if v_isSharedCheck_3028_ == 0 {
                                v___x_3023_ = v___x_3020_;
                                v_isShared_3024_ = v_isSharedCheck_3028_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_3021_);
                                crate::leanh::lean_dec(v___x_3020_);
                                v___x_3023_ = crate::leanh::lean_box(0);
                                v_isShared_3024_ = v_isSharedCheck_3028_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_3020_);
                            v___x_3029_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7_once), _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7);
                            v___x_3030_ = l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6(v___x_3029_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
                            if crate::leanh::lean_obj_tag(v___x_3030_) == 0 {
                                v_a_3031_ = crate::leanh::lean_ctor_get(v___x_3030_, 0);
                                v_isSharedCheck_3039_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3030_)) as u8;
                                if v_isSharedCheck_3039_ == 0 {
                                    v___x_3033_ = v___x_3030_;
                                    v_isShared_3034_ = v_isSharedCheck_3039_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3031_);
                                    crate::leanh::lean_dec(v___x_3030_);
                                    v___x_3033_ = crate::leanh::lean_box(0);
                                    v_isShared_3034_ = v_isSharedCheck_3039_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_constName_3000_);
                                v_a_3040_ = crate::leanh::lean_ctor_get(v___x_3030_, 0);
                                v_isSharedCheck_3047_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3030_)) as u8;
                                if v_isSharedCheck_3047_ == 0 {
                                    v___x_3042_ = v___x_3030_;
                                    v_isShared_3043_ = v_isSharedCheck_3047_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3040_);
                                    crate::leanh::lean_dec(v___x_3030_);
                                    v___x_3042_ = crate::leanh::lean_box(0);
                                    v_isShared_3043_ = v_isSharedCheck_3047_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_3018_);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3017_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3007_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1_once
                    ),
                    _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1,
                );
                v___x_3008_ = 0;
                v___x_3009_ = l_Lean_MessageData_ofConstName(v_constName_3000_, v___x_3008_);
                v___x_3010_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3010_, 0, v___x_3007_);
                crate::leanh::lean_ctor_set(v___x_3010_, 1, v___x_3009_);
                v___x_3011_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3_once
                    ),
                    _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3,
                );
                v___x_3012_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3012_, 0, v___x_3010_);
                crate::leanh::lean_ctor_set(v___x_3012_, 1, v___x_3011_);
                v___x_3013_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v___x_3012_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
                return v___x_3013_;
            }
            2 => {
                if v_isShared_3024_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3023_, 0);
                    v___x_3026_ = v___x_3023_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3027_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_val_3021_);
                    v___x_3026_ = v_reuseFailAlloc_3027_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3026_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_3031_) == 0 {
                    crate::leanh::lean_del_object(v___x_3033_);
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_constName_3000_);
                    v_val_3035_ = crate::leanh::lean_ctor_get(v_a_3031_, 0);
                    crate::leanh::lean_inc(v_val_3035_);
                    crate::leanh::lean_dec_ref_known(v_a_3031_, 1);
                    if v_isShared_3034_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3033_, 0, v_val_3035_);
                        v___x_3037_ = v___x_3033_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3038_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_val_3035_);
                        v___x_3037_ = v_reuseFailAlloc_3038_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_3037_;
            }
            6 => {
                if v_isShared_3043_ == 0 {
                    v___x_3045_ = v___x_3042_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3046_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_a_3040_);
                    v___x_3045_ = v_reuseFailAlloc_3046_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3045_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___boxed(
    mut v_constName_3048_: *mut crate::leanh::LeanObject,
    mut v___y_3049_: *mut crate::leanh::LeanObject,
    mut v___y_3050_: *mut crate::leanh::LeanObject,
    mut v___y_3051_: *mut crate::leanh::LeanObject,
    mut v___y_3052_: *mut crate::leanh::LeanObject,
    mut v___y_3053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3054_ = l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4(
        v_constName_3048_,
        v___y_3049_,
        v___y_3050_,
        v___y_3051_,
        v___y_3052_,
    );
    crate::leanh::lean_dec(v___y_3052_);
    crate::leanh::lean_dec_ref(v___y_3051_);
    crate::leanh::lean_dec(v___y_3050_);
    crate::leanh::lean_dec_ref(v___y_3049_);
    return v_res_3054_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___lam__0(
    mut v_cidx_3055_: *mut crate::leanh::LeanObject,
    mut v___x_3056_: u8,
    mut v___x_3057_: u8,
    mut v___x_3058_: u8,
    mut v_ys_3059_: *mut crate::leanh::LeanObject,
    mut v_x_3060_: *mut crate::leanh::LeanObject,
    mut v___y_3061_: *mut crate::leanh::LeanObject,
    mut v___y_3062_: *mut crate::leanh::LeanObject,
    mut v___y_3063_: *mut crate::leanh::LeanObject,
    mut v___y_3064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3066_ = l_Lean_mkRawNatLit(v_cidx_3055_);
    v___x_3067_ = l_Lean_Meta_mkLambdaFVars(
        v_ys_3059_,
        v___x_3066_,
        v___x_3056_,
        v___x_3057_,
        v___x_3056_,
        v___x_3057_,
        v___x_3058_,
        v___y_3061_,
        v___y_3062_,
        v___y_3063_,
        v___y_3064_,
    );
    return v___x_3067_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___lam__0___boxed(
    mut v_cidx_3068_: *mut crate::leanh::LeanObject,
    mut v___x_3069_: *mut crate::leanh::LeanObject,
    mut v___x_3070_: *mut crate::leanh::LeanObject,
    mut v___x_3071_: *mut crate::leanh::LeanObject,
    mut v_ys_3072_: *mut crate::leanh::LeanObject,
    mut v_x_3073_: *mut crate::leanh::LeanObject,
    mut v___y_3074_: *mut crate::leanh::LeanObject,
    mut v___y_3075_: *mut crate::leanh::LeanObject,
    mut v___y_3076_: *mut crate::leanh::LeanObject,
    mut v___y_3077_: *mut crate::leanh::LeanObject,
    mut v___y_3078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_34834__boxed_3079_: u8 = 0;
    let mut v___x_34835__boxed_3080_: u8 = 0;
    let mut v___x_34836__boxed_3081_: u8 = 0;
    let mut v_res_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_34834__boxed_3079_ = (crate::leanh::lean_unbox(v___x_3069_) as u8);
    v___x_34835__boxed_3080_ = (crate::leanh::lean_unbox(v___x_3070_) as u8);
    v___x_34836__boxed_3081_ = (crate::leanh::lean_unbox(v___x_3071_) as u8);
    v_res_3082_ = l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___lam__0(
        v_cidx_3068_,
        v___x_34834__boxed_3079_,
        v___x_34835__boxed_3080_,
        v___x_34836__boxed_3081_,
        v_ys_3072_,
        v_x_3073_,
        v___y_3074_,
        v___y_3075_,
        v___y_3076_,
        v___y_3077_,
    );
    crate::leanh::lean_dec(v___y_3077_);
    crate::leanh::lean_dec_ref(v___y_3076_);
    crate::leanh::lean_dec(v___y_3075_);
    crate::leanh::lean_dec_ref(v___y_3074_);
    crate::leanh::lean_dec_ref(v_x_3073_);
    crate::leanh::lean_dec_ref(v_ys_3072_);
    return v_res_3082_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg(
    mut v___x_3083_: u8,
    mut v___x_3084_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3085_: *mut crate::leanh::LeanObject,
    mut v_b_3086_: *mut crate::leanh::LeanObject,
    mut v___y_3087_: *mut crate::leanh::LeanObject,
    mut v___y_3088_: *mut crate::leanh::LeanObject,
    mut v___y_3089_: *mut crate::leanh::LeanObject,
    mut v___y_3090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3105_: u8 = 0;
    let mut v___x_3106_: u8 = 0;
    let mut v___x_3107_: u8 = 0;
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3119_: u8 = 0;
    let mut v_a_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3123_: u8 = 0;
    let mut v___x_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3127_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_3085_) == 0 {
                    v___x_3092_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3092_, 0, v_b_3086_);
                    return v___x_3092_;
                } else {
                    v_head_3093_ = crate::leanh::lean_ctor_get(v_as_x27_3085_, 0);
                    v_tail_3094_ = crate::leanh::lean_ctor_get(v_as_x27_3085_, 1);
                    crate::leanh::lean_inc(v_head_3093_);
                    v___x_3095_ = l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4(
                        v_head_3093_,
                        v___y_3087_,
                        v___y_3088_,
                        v___y_3089_,
                        v___y_3090_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3095_) == 0 {
                        v_a_3096_ = crate::leanh::lean_ctor_get(v___x_3095_, 0);
                        crate::leanh::lean_inc(v_a_3096_);
                        crate::leanh::lean_dec_ref_known(v___x_3095_, 1);
                        v_toConstantVal_3097_ = crate::leanh::lean_ctor_get(v_a_3096_, 0);
                        crate::leanh::lean_inc_ref(v_toConstantVal_3097_);
                        v_cidx_3098_ = crate::leanh::lean_ctor_get(v_a_3096_, 2);
                        crate::leanh::lean_inc(v_cidx_3098_);
                        v_numFields_3099_ = crate::leanh::lean_ctor_get(v_a_3096_, 4);
                        crate::leanh::lean_inc(v_numFields_3099_);
                        crate::leanh::lean_dec(v_a_3096_);
                        v_type_3100_ = crate::leanh::lean_ctor_get(v_toConstantVal_3097_, 2);
                        crate::leanh::lean_inc_ref(v_type_3100_);
                        crate::leanh::lean_dec_ref(v_toConstantVal_3097_);
                        v___x_3101_ = l_Lean_Meta_instantiateForall(
                            v_type_3100_,
                            v___x_3084_,
                            v___y_3087_,
                            v___y_3088_,
                            v___y_3089_,
                            v___y_3090_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3101_) == 0 {
                            v_a_3102_ = crate::leanh::lean_ctor_get(v___x_3101_, 0);
                            v_isSharedCheck_3119_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3101_)) as u8;
                            if v_isSharedCheck_3119_ == 0 {
                                v___x_3104_ = v___x_3101_;
                                v_isShared_3105_ = v_isSharedCheck_3119_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3102_);
                                crate::leanh::lean_dec(v___x_3101_);
                                v___x_3104_ = crate::leanh::lean_box(0);
                                v_isShared_3105_ = v_isSharedCheck_3119_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_numFields_3099_);
                            crate::leanh::lean_dec(v_cidx_3098_);
                            crate::leanh::lean_dec_ref(v_b_3086_);
                            return v___x_3101_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_3086_);
                        v_a_3120_ = crate::leanh::lean_ctor_get(v___x_3095_, 0);
                        v_isSharedCheck_3127_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3095_)) as u8;
                        if v_isSharedCheck_3127_ == 0 {
                            v___x_3122_ = v___x_3095_;
                            v_isShared_3123_ = v_isSharedCheck_3127_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3120_);
                            crate::leanh::lean_dec(v___x_3095_);
                            v___x_3122_ = crate::leanh::lean_box(0);
                            v_isShared_3123_ = v_isSharedCheck_3127_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3106_ = 0;
                v___x_3107_ = 1;
                v___x_3108_ = crate::leanh::lean_box((v___x_3106_) as usize);
                v___x_3109_ = crate::leanh::lean_box((v___x_3083_) as usize);
                v___x_3110_ = crate::leanh::lean_box((v___x_3107_) as usize);
                v___f_3111_ = crate::leanh::lean_alloc_closure(
                    l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    11,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_3111_, 0, v_cidx_3098_);
                crate::leanh::lean_closure_set(v___f_3111_, 1, v___x_3108_);
                crate::leanh::lean_closure_set(v___f_3111_, 2, v___x_3109_);
                crate::leanh::lean_closure_set(v___f_3111_, 3, v___x_3110_);
                if v_isShared_3105_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3104_, 1);
                    crate::leanh::lean_ctor_set(v___x_3104_, 0, v_numFields_3099_);
                    v___x_3113_ = v___x_3104_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3118_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_numFields_3099_);
                    v___x_3113_ = v_reuseFailAlloc_3118_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3114_ =
                    l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg(
                        v_a_3102_,
                        v___x_3113_,
                        v___f_3111_,
                        v___x_3106_,
                        v___x_3106_,
                        v___y_3087_,
                        v___y_3088_,
                        v___y_3089_,
                        v___y_3090_,
                    );
                if crate::leanh::lean_obj_tag(v___x_3114_) == 0 {
                    v_a_3115_ = crate::leanh::lean_ctor_get(v___x_3114_, 0);
                    crate::leanh::lean_inc(v_a_3115_);
                    crate::leanh::lean_dec_ref_known(v___x_3114_, 1);
                    v___x_3116_ = l_Lean_Expr_app___override(v_b_3086_, v_a_3115_);
                    v_as_x27_3085_ = v_tail_3094_;
                    v_b_3086_ = v___x_3116_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_b_3086_);
                    return v___x_3114_;
                }
            }
            3 => {
                if v_isShared_3123_ == 0 {
                    v___x_3125_ = v___x_3122_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3126_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3120_);
                    v___x_3125_ = v_reuseFailAlloc_3126_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3125_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___boxed(
    mut v___x_3128_: *mut crate::leanh::LeanObject,
    mut v___x_3129_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3130_: *mut crate::leanh::LeanObject,
    mut v_b_3131_: *mut crate::leanh::LeanObject,
    mut v___y_3132_: *mut crate::leanh::LeanObject,
    mut v___y_3133_: *mut crate::leanh::LeanObject,
    mut v___y_3134_: *mut crate::leanh::LeanObject,
    mut v___y_3135_: *mut crate::leanh::LeanObject,
    mut v___y_3136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_34865__boxed_3137_: u8 = 0;
    let mut v_res_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_34865__boxed_3137_ = (crate::leanh::lean_unbox(v___x_3128_) as u8);
    v_res_3138_ = l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg(
        v___x_34865__boxed_3137_,
        v___x_3129_,
        v_as_x27_3130_,
        v_b_3131_,
        v___y_3132_,
        v___y_3133_,
        v___y_3134_,
        v___y_3135_,
    );
    crate::leanh::lean_dec(v___y_3135_);
    crate::leanh::lean_dec_ref(v___y_3134_);
    crate::leanh::lean_dec(v___y_3133_);
    crate::leanh::lean_dec_ref(v___y_3132_);
    crate::leanh::lean_dec(v_as_x27_3130_);
    crate::leanh::lean_dec_ref(v___x_3129_);
    return v_res_3138_;
}
pub unsafe fn _init_l_mkCtorIdx___lam__0___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3139_ = crate::leanh::lean_box(0);
    v___x_3140_ = l_Lean_Level_succ___override(v___x_3139_);
    return v___x_3140_;
}
pub unsafe fn l_mkCtorIdx___lam__0(
    mut v_xs_3141_: *mut crate::leanh::LeanObject,
    mut v___x_3142_: u8,
    mut v___x_3143_: u8,
    mut v___x_3144_: u8,
    mut v_val_3145_: *mut crate::leanh::LeanObject,
    mut v___x_3146_: *mut crate::leanh::LeanObject,
    mut v___x_3147_: *mut crate::leanh::LeanObject,
    mut v___x_3148_: *mut crate::leanh::LeanObject,
    mut v___x_3149_: *mut crate::leanh::LeanObject,
    mut v___x_3150_: *mut crate::leanh::LeanObject,
    mut v_ctors_3151_: *mut crate::leanh::LeanObject,
    mut v___x_3152_: *mut crate::leanh::LeanObject,
    mut v_x_3153_: *mut crate::leanh::LeanObject,
    mut v___y_3154_: *mut crate::leanh::LeanObject,
    mut v___y_3155_: *mut crate::leanh::LeanObject,
    mut v___y_3156_: *mut crate::leanh::LeanObject,
    mut v___y_3157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_value_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: u8 = 0;
    let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3163_ = l_Lean_InductiveVal_numCtors(v_val_3145_);
                v___x_3164_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3165_ = lean_nat_dec_eq(v___x_3163_, v___x_3164_);
                crate::leanh::lean_dec(v___x_3163_);
                if v___x_3165_ == 0 {
                    crate::leanh::lean_dec(v___x_3152_);
                    crate::leanh::lean_inc_ref(v_x_3153_);
                    crate::leanh::lean_inc_ref(v___x_3146_);
                    v___x_3166_ = lean_array_push(v___x_3146_, v_x_3153_);
                    v___x_3167_ = l_Lean_Meta_mkLambdaFVars(
                        v___x_3166_,
                        v___x_3147_,
                        v___x_3142_,
                        v___x_3143_,
                        v___x_3142_,
                        v___x_3143_,
                        v___x_3144_,
                        v___y_3154_,
                        v___y_3155_,
                        v___y_3156_,
                        v___y_3157_,
                    );
                    crate::leanh::lean_dec_ref(v___x_3166_);
                    if crate::leanh::lean_obj_tag(v___x_3167_) == 0 {
                        v_a_3168_ = crate::leanh::lean_ctor_get(v___x_3167_, 0);
                        crate::leanh::lean_inc(v_a_3168_);
                        crate::leanh::lean_dec_ref_known(v___x_3167_, 1);
                        v___x_3169_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_mkCtorIdx___lam__0___closed__0),
                            core::ptr::addr_of_mut!(l_mkCtorIdx___lam__0___closed__0_once),
                            _init_l_mkCtorIdx___lam__0___closed__0,
                        );
                        v___x_3170_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3170_, 0, v___x_3169_);
                        crate::leanh::lean_ctor_set(v___x_3170_, 1, v___x_3148_);
                        v___x_3171_ = l_Lean_mkConst(v___x_3149_, v___x_3170_);
                        v___x_3172_ = l_Lean_mkAppN(v___x_3171_, v___x_3150_);
                        v___x_3173_ = l_Lean_Expr_app___override(v___x_3172_, v_a_3168_);
                        v___x_3174_ = l_Lean_mkAppN(v___x_3173_, v___x_3146_);
                        crate::leanh::lean_dec_ref(v___x_3146_);
                        crate::leanh::lean_inc_ref(v_x_3153_);
                        v___x_3175_ = l_Lean_Expr_app___override(v___x_3174_, v_x_3153_);
                        v___x_3176_ = l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg(
                            v___x_3143_,
                            v___x_3150_,
                            v_ctors_3151_,
                            v___x_3175_,
                            v___y_3154_,
                            v___y_3155_,
                            v___y_3156_,
                            v___y_3157_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3176_) == 0 {
                            v_a_3177_ = crate::leanh::lean_ctor_get(v___x_3176_, 0);
                            crate::leanh::lean_inc(v_a_3177_);
                            crate::leanh::lean_dec_ref_known(v___x_3176_, 1);
                            v_value_3160_ = v_a_3177_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_x_3153_);
                            crate::leanh::lean_dec_ref(v_xs_3141_);
                            return v___x_3176_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_x_3153_);
                        crate::leanh::lean_dec(v___x_3149_);
                        crate::leanh::lean_dec(v___x_3148_);
                        crate::leanh::lean_dec_ref(v___x_3146_);
                        crate::leanh::lean_dec_ref(v_xs_3141_);
                        return v___x_3167_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3149_);
                    crate::leanh::lean_dec(v___x_3148_);
                    crate::leanh::lean_dec_ref(v___x_3147_);
                    crate::leanh::lean_dec_ref(v___x_3146_);
                    v___x_3178_ = l_Lean_mkRawNatLit(v___x_3152_);
                    v_value_3160_ = v___x_3178_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3161_ = lean_array_push(v_xs_3141_, v_x_3153_);
                v___x_3162_ = l_Lean_Meta_mkLambdaFVars(
                    v___x_3161_,
                    v_value_3160_,
                    v___x_3142_,
                    v___x_3143_,
                    v___x_3142_,
                    v___x_3143_,
                    v___x_3144_,
                    v___y_3154_,
                    v___y_3155_,
                    v___y_3156_,
                    v___y_3157_,
                );
                crate::leanh::lean_dec_ref(v___x_3161_);
                return v___x_3162_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_mkCtorIdx___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_xs_3179_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_3180_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_3181_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_3182_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_val_3183_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_3184_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_3185_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_3186_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_3187_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_3188_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_ctors_3189_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_3190_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_x_3191_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_3192_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_3193_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_3194_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_3195_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_3196_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___x_34956__boxed_3197_: u8 = 0;
    let mut v___x_34957__boxed_3198_: u8 = 0;
    let mut v___x_34958__boxed_3199_: u8 = 0;
    let mut v_res_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_34956__boxed_3197_ = (crate::leanh::lean_unbox(v___x_3180_) as u8);
    v___x_34957__boxed_3198_ = (crate::leanh::lean_unbox(v___x_3181_) as u8);
    v___x_34958__boxed_3199_ = (crate::leanh::lean_unbox(v___x_3182_) as u8);
    v_res_3200_ = l_mkCtorIdx___lam__0(
        v_xs_3179_,
        v___x_34956__boxed_3197_,
        v___x_34957__boxed_3198_,
        v___x_34958__boxed_3199_,
        v_val_3183_,
        v___x_3184_,
        v___x_3185_,
        v___x_3186_,
        v___x_3187_,
        v___x_3188_,
        v_ctors_3189_,
        v___x_3190_,
        v_x_3191_,
        v___y_3192_,
        v___y_3193_,
        v___y_3194_,
        v___y_3195_,
    );
    crate::leanh::lean_dec(v___y_3195_);
    crate::leanh::lean_dec_ref(v___y_3194_);
    crate::leanh::lean_dec(v___y_3193_);
    crate::leanh::lean_dec_ref(v___y_3192_);
    crate::leanh::lean_dec(v_ctors_3189_);
    crate::leanh::lean_dec_ref(v___x_3188_);
    crate::leanh::lean_dec_ref(v_val_3183_);
    return v_res_3200_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3201_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3201_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3202_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0);
    v___x_3203_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3203_, 0, v___x_3202_);
    return v___x_3203_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3204_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1);
    v___x_3205_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3206_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3206_, 0, v___x_3205_);
    crate::leanh::lean_ctor_set(v___x_3206_, 1, v___x_3205_);
    crate::leanh::lean_ctor_set(v___x_3206_, 2, v___x_3205_);
    crate::leanh::lean_ctor_set(v___x_3206_, 3, v___x_3205_);
    crate::leanh::lean_ctor_set(v___x_3206_, 4, v___x_3204_);
    crate::leanh::lean_ctor_set(v___x_3206_, 5, v___x_3204_);
    crate::leanh::lean_ctor_set(v___x_3206_, 6, v___x_3204_);
    crate::leanh::lean_ctor_set(v___x_3206_, 7, v___x_3204_);
    crate::leanh::lean_ctor_set(v___x_3206_, 8, v___x_3204_);
    crate::leanh::lean_ctor_set(v___x_3206_, 9, v___x_3204_);
    return v___x_3206_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3207_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3208_ = lean_mk_empty_array_with_capacity(v___x_3207_);
    v___x_3209_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3209_, 0, v___x_3208_);
    return v___x_3209_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3210_: usize = 0;
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3210_ = 5usize;
    v___x_3211_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3212_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3213_ = lean_mk_empty_array_with_capacity(v___x_3212_);
    v___x_3214_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3);
    v___x_3215_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_3215_, 0, v___x_3214_);
    crate::leanh::lean_ctor_set(v___x_3215_, 1, v___x_3213_);
    crate::leanh::lean_ctor_set(v___x_3215_, 2, v___x_3211_);
    crate::leanh::lean_ctor_set(v___x_3215_, 3, v___x_3211_);
    crate::leanh::lean_ctor_set_usize(v___x_3215_, 4, v___x_3210_);
    return v___x_3215_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3216_ = crate::leanh::lean_box(1);
    v___x_3217_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4);
    v___x_3218_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1);
    v___x_3219_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3219_, 0, v___x_3218_);
    crate::leanh::lean_ctor_set(v___x_3219_, 1, v___x_3217_);
    crate::leanh::lean_ctor_set(v___x_3219_, 2, v___x_3216_);
    return v___x_3219_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3221_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__6;
    v___x_3222_ = l_Lean_stringToMessageData(v___x_3221_);
    return v___x_3222_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3224_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__8;
    v___x_3225_ = l_Lean_stringToMessageData(v___x_3224_);
    return v___x_3225_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3227_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__10;
    v___x_3228_ = l_Lean_stringToMessageData(v___x_3227_);
    return v___x_3228_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3230_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__12;
    v___x_3231_ = l_Lean_stringToMessageData(v___x_3230_);
    return v___x_3231_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3233_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__14;
    v___x_3234_ = l_Lean_stringToMessageData(v___x_3233_);
    return v___x_3234_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3236_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__16;
    v___x_3237_ = l_Lean_stringToMessageData(v___x_3236_);
    return v___x_3237_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3239_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__18;
    v___x_3240_ = l_Lean_stringToMessageData(v___x_3239_);
    return v___x_3240_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(
    mut v_msg_3241_: *mut crate::leanh::LeanObject,
    mut v_declHint_3242_: *mut crate::leanh::LeanObject,
    mut v___y_3243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: u8 = 0;
    let mut v_isExporting_3248_: u8 = 0;
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: u8 = 0;
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3270_: u8 = 0;
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: u8 = 0;
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3302_: u8 = 0;
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3245_ = lean_st_ref_get(v___y_3243_);
                v_env_3246_ = crate::leanh::lean_ctor_get(v___x_3245_, 0);
                crate::leanh::lean_inc_ref(v_env_3246_);
                crate::leanh::lean_dec(v___x_3245_);
                v___x_3247_ = l_Lean_Name_isAnonymous(v_declHint_3242_);
                if v___x_3247_ == 0 {
                    v_isExporting_3248_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_3246_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_3248_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_3246_);
                        crate::leanh::lean_dec(v_declHint_3242_);
                        v___x_3249_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3249_, 0, v_msg_3241_);
                        return v___x_3249_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_3246_);
                        v___x_3250_ = l_Lean_Environment_setExporting(v_env_3246_, v___x_3247_);
                        crate::leanh::lean_inc(v_declHint_3242_);
                        crate::leanh::lean_inc_ref(v___x_3250_);
                        v___x_3251_ = l_Lean_Environment_contains(
                            v___x_3250_,
                            v_declHint_3242_,
                            v_isExporting_3248_,
                        );
                        if v___x_3251_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_3250_);
                            crate::leanh::lean_dec_ref(v_env_3246_);
                            crate::leanh::lean_dec(v_declHint_3242_);
                            v___x_3252_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3252_, 0, v_msg_3241_);
                            return v___x_3252_;
                        } else {
                            v___x_3253_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2);
                            v___x_3254_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5);
                            v___x_3255_ = l_Lean_Options_empty;
                            v___x_3256_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3256_, 0, v___x_3250_);
                            crate::leanh::lean_ctor_set(v___x_3256_, 1, v___x_3253_);
                            crate::leanh::lean_ctor_set(v___x_3256_, 2, v___x_3254_);
                            crate::leanh::lean_ctor_set(v___x_3256_, 3, v___x_3255_);
                            crate::leanh::lean_inc(v_declHint_3242_);
                            v___x_3257_ =
                                l_Lean_MessageData_ofConstName(v_declHint_3242_, v___x_3247_);
                            v_c_3258_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_3258_, 0, v___x_3256_);
                            crate::leanh::lean_ctor_set(v_c_3258_, 1, v___x_3257_);
                            v___x_3259_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_3246_,
                                v_declHint_3242_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3259_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_3246_);
                                crate::leanh::lean_dec(v_declHint_3242_);
                                v___x_3260_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7);
                                v___x_3261_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3261_, 0, v___x_3260_);
                                crate::leanh::lean_ctor_set(v___x_3261_, 1, v_c_3258_);
                                v___x_3262_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9);
                                v___x_3263_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3263_, 0, v___x_3261_);
                                crate::leanh::lean_ctor_set(v___x_3263_, 1, v___x_3262_);
                                v___x_3264_ = l_Lean_MessageData_note(v___x_3263_);
                                v___x_3265_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3265_, 0, v_msg_3241_);
                                crate::leanh::lean_ctor_set(v___x_3265_, 1, v___x_3264_);
                                v___x_3266_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3266_, 0, v___x_3265_);
                                return v___x_3266_;
                            } else {
                                v_val_3267_ = crate::leanh::lean_ctor_get(v___x_3259_, 0);
                                v_isSharedCheck_3302_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3259_)) as u8;
                                if v_isSharedCheck_3302_ == 0 {
                                    v___x_3269_ = v___x_3259_;
                                    v_isShared_3270_ = v_isSharedCheck_3302_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_3267_);
                                    crate::leanh::lean_dec(v___x_3259_);
                                    v___x_3269_ = crate::leanh::lean_box(0);
                                    v_isShared_3270_ = v_isSharedCheck_3302_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_3246_);
                    crate::leanh::lean_dec(v_declHint_3242_);
                    v___x_3303_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3303_, 0, v_msg_3241_);
                    return v___x_3303_;
                }
            }
            1 => {
                v___x_3271_ = crate::leanh::lean_box(0);
                v___x_3272_ = l_Lean_Environment_header(v_env_3246_);
                crate::leanh::lean_dec_ref(v_env_3246_);
                v___x_3273_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3272_);
                v_mod_3274_ = lean_array_get(v___x_3271_, v___x_3273_, v_val_3267_);
                crate::leanh::lean_dec(v_val_3267_);
                crate::leanh::lean_dec_ref(v___x_3273_);
                v___x_3275_ = l_Lean_isPrivateName(v_declHint_3242_);
                crate::leanh::lean_dec(v_declHint_3242_);
                if v___x_3275_ == 0 {
                    v___x_3276_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11);
                    v___x_3277_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3277_, 0, v___x_3276_);
                    crate::leanh::lean_ctor_set(v___x_3277_, 1, v_c_3258_);
                    v___x_3278_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13);
                    v___x_3279_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3279_, 0, v___x_3277_);
                    crate::leanh::lean_ctor_set(v___x_3279_, 1, v___x_3278_);
                    v___x_3280_ = l_Lean_MessageData_ofName(v_mod_3274_);
                    v___x_3281_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3281_, 0, v___x_3279_);
                    crate::leanh::lean_ctor_set(v___x_3281_, 1, v___x_3280_);
                    v___x_3282_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15);
                    v___x_3283_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3283_, 0, v___x_3281_);
                    crate::leanh::lean_ctor_set(v___x_3283_, 1, v___x_3282_);
                    v___x_3284_ = l_Lean_MessageData_note(v___x_3283_);
                    v___x_3285_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3285_, 0, v_msg_3241_);
                    crate::leanh::lean_ctor_set(v___x_3285_, 1, v___x_3284_);
                    if v_isShared_3270_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3269_, 0);
                        crate::leanh::lean_ctor_set(v___x_3269_, 0, v___x_3285_);
                        v___x_3287_ = v___x_3269_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3288_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3288_, 0, v___x_3285_);
                        v___x_3287_ = v_reuseFailAlloc_3288_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3289_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7);
                    v___x_3290_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3290_, 0, v___x_3289_);
                    crate::leanh::lean_ctor_set(v___x_3290_, 1, v_c_3258_);
                    v___x_3291_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17);
                    v___x_3292_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3292_, 0, v___x_3290_);
                    crate::leanh::lean_ctor_set(v___x_3292_, 1, v___x_3291_);
                    v___x_3293_ = l_Lean_MessageData_ofName(v_mod_3274_);
                    v___x_3294_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3294_, 0, v___x_3292_);
                    crate::leanh::lean_ctor_set(v___x_3294_, 1, v___x_3293_);
                    v___x_3295_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19);
                    v___x_3296_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3296_, 0, v___x_3294_);
                    crate::leanh::lean_ctor_set(v___x_3296_, 1, v___x_3295_);
                    v___x_3297_ = l_Lean_MessageData_note(v___x_3296_);
                    v___x_3298_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3298_, 0, v_msg_3241_);
                    crate::leanh::lean_ctor_set(v___x_3298_, 1, v___x_3297_);
                    if v_isShared_3270_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3269_, 0);
                        crate::leanh::lean_ctor_set(v___x_3269_, 0, v___x_3298_);
                        v___x_3300_ = v___x_3269_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3301_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3298_);
                        v___x_3300_ = v_reuseFailAlloc_3301_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3287_;
            }
            3 => {
                return v___x_3300_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___boxed(
    mut v_msg_3304_: *mut crate::leanh::LeanObject,
    mut v_declHint_3305_: *mut crate::leanh::LeanObject,
    mut v___y_3306_: *mut crate::leanh::LeanObject,
    mut v___y_3307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3308_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(v_msg_3304_, v_declHint_3305_, v___y_3306_);
    crate::leanh::lean_dec(v___y_3306_);
    return v_res_3308_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(
    mut v_msg_3309_: *mut crate::leanh::LeanObject,
    mut v_declHint_3310_: *mut crate::leanh::LeanObject,
    mut v___y_3311_: *mut crate::leanh::LeanObject,
    mut v___y_3312_: *mut crate::leanh::LeanObject,
    mut v___y_3313_: *mut crate::leanh::LeanObject,
    mut v___y_3314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3320_: u8 = 0;
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3326_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3316_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(v_msg_3309_, v_declHint_3310_, v___y_3314_);
                v_a_3317_ = crate::leanh::lean_ctor_get(v___x_3316_, 0);
                v_isSharedCheck_3326_ = (!crate::leanh::lean_is_exclusive(v___x_3316_)) as u8;
                if v_isSharedCheck_3326_ == 0 {
                    v___x_3319_ = v___x_3316_;
                    v_isShared_3320_ = v_isSharedCheck_3326_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3317_);
                    crate::leanh::lean_dec(v___x_3316_);
                    v___x_3319_ = crate::leanh::lean_box(0);
                    v_isShared_3320_ = v_isSharedCheck_3326_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3321_ = l_Lean_unknownIdentifierMessageTag;
                v___x_3322_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3322_, 0, v___x_3321_);
                crate::leanh::lean_ctor_set(v___x_3322_, 1, v_a_3317_);
                if v_isShared_3320_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3319_, 0, v___x_3322_);
                    v___x_3324_ = v___x_3319_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3325_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3325_, 0, v___x_3322_);
                    v___x_3324_ = v_reuseFailAlloc_3325_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3324_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26___boxed(
    mut v_msg_3327_: *mut crate::leanh::LeanObject,
    mut v_declHint_3328_: *mut crate::leanh::LeanObject,
    mut v___y_3329_: *mut crate::leanh::LeanObject,
    mut v___y_3330_: *mut crate::leanh::LeanObject,
    mut v___y_3331_: *mut crate::leanh::LeanObject,
    mut v___y_3332_: *mut crate::leanh::LeanObject,
    mut v___y_3333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3334_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(v_msg_3327_, v_declHint_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
    crate::leanh::lean_dec(v___y_3332_);
    crate::leanh::lean_dec_ref(v___y_3331_);
    crate::leanh::lean_dec(v___y_3330_);
    crate::leanh::lean_dec_ref(v___y_3329_);
    return v_res_3334_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(
    mut v_ref_3335_: *mut crate::leanh::LeanObject,
    mut v_msg_3336_: *mut crate::leanh::LeanObject,
    mut v___y_3337_: *mut crate::leanh::LeanObject,
    mut v___y_3338_: *mut crate::leanh::LeanObject,
    mut v___y_3339_: *mut crate::leanh::LeanObject,
    mut v___y_3340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3354_: u8 = 0;
    let mut v_cancelTk_x3f_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3356_: u8 = 0;
    let mut v_inheritedTraceOptions_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_3342_ = crate::leanh::lean_ctor_get(v___y_3339_, 0);
    v_fileMap_3343_ = crate::leanh::lean_ctor_get(v___y_3339_, 1);
    v_options_3344_ = crate::leanh::lean_ctor_get(v___y_3339_, 2);
    v_currRecDepth_3345_ = crate::leanh::lean_ctor_get(v___y_3339_, 3);
    v_maxRecDepth_3346_ = crate::leanh::lean_ctor_get(v___y_3339_, 4);
    v_ref_3347_ = crate::leanh::lean_ctor_get(v___y_3339_, 5);
    v_currNamespace_3348_ = crate::leanh::lean_ctor_get(v___y_3339_, 6);
    v_openDecls_3349_ = crate::leanh::lean_ctor_get(v___y_3339_, 7);
    v_initHeartbeats_3350_ = crate::leanh::lean_ctor_get(v___y_3339_, 8);
    v_maxHeartbeats_3351_ = crate::leanh::lean_ctor_get(v___y_3339_, 9);
    v_quotContext_3352_ = crate::leanh::lean_ctor_get(v___y_3339_, 10);
    v_currMacroScope_3353_ = crate::leanh::lean_ctor_get(v___y_3339_, 11);
    v_diag_3354_ = crate::leanh::lean_ctor_get_uint8(
        v___y_3339_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3355_ = crate::leanh::lean_ctor_get(v___y_3339_, 12);
    v_suppressElabErrors_3356_ = crate::leanh::lean_ctor_get_uint8(
        v___y_3339_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3357_ = crate::leanh::lean_ctor_get(v___y_3339_, 13);
    v_ref_3358_ = l_Lean_replaceRef(v_ref_3335_, v_ref_3347_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_3357_);
    crate::leanh::lean_inc(v_cancelTk_x3f_3355_);
    crate::leanh::lean_inc(v_currMacroScope_3353_);
    crate::leanh::lean_inc(v_quotContext_3352_);
    crate::leanh::lean_inc(v_maxHeartbeats_3351_);
    crate::leanh::lean_inc(v_initHeartbeats_3350_);
    crate::leanh::lean_inc(v_openDecls_3349_);
    crate::leanh::lean_inc(v_currNamespace_3348_);
    crate::leanh::lean_inc(v_maxRecDepth_3346_);
    crate::leanh::lean_inc(v_currRecDepth_3345_);
    crate::leanh::lean_inc_ref(v_options_3344_);
    crate::leanh::lean_inc_ref(v_fileMap_3343_);
    crate::leanh::lean_inc_ref(v_fileName_3342_);
    v___x_3359_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_3359_, 0, v_fileName_3342_);
    crate::leanh::lean_ctor_set(v___x_3359_, 1, v_fileMap_3343_);
    crate::leanh::lean_ctor_set(v___x_3359_, 2, v_options_3344_);
    crate::leanh::lean_ctor_set(v___x_3359_, 3, v_currRecDepth_3345_);
    crate::leanh::lean_ctor_set(v___x_3359_, 4, v_maxRecDepth_3346_);
    crate::leanh::lean_ctor_set(v___x_3359_, 5, v_ref_3358_);
    crate::leanh::lean_ctor_set(v___x_3359_, 6, v_currNamespace_3348_);
    crate::leanh::lean_ctor_set(v___x_3359_, 7, v_openDecls_3349_);
    crate::leanh::lean_ctor_set(v___x_3359_, 8, v_initHeartbeats_3350_);
    crate::leanh::lean_ctor_set(v___x_3359_, 9, v_maxHeartbeats_3351_);
    crate::leanh::lean_ctor_set(v___x_3359_, 10, v_quotContext_3352_);
    crate::leanh::lean_ctor_set(v___x_3359_, 11, v_currMacroScope_3353_);
    crate::leanh::lean_ctor_set(v___x_3359_, 12, v_cancelTk_x3f_3355_);
    crate::leanh::lean_ctor_set(v___x_3359_, 13, v_inheritedTraceOptions_3357_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3359_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_3354_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3359_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3356_,
    );
    v___x_3360_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v_msg_3336_, v___y_3337_, v___y_3338_, v___x_3359_, v___y_3340_);
    crate::leanh::lean_dec_ref_known(v___x_3359_, 14);
    return v___x_3360_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg___boxed(
    mut v_ref_3361_: *mut crate::leanh::LeanObject,
    mut v_msg_3362_: *mut crate::leanh::LeanObject,
    mut v___y_3363_: *mut crate::leanh::LeanObject,
    mut v___y_3364_: *mut crate::leanh::LeanObject,
    mut v___y_3365_: *mut crate::leanh::LeanObject,
    mut v___y_3366_: *mut crate::leanh::LeanObject,
    mut v___y_3367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3368_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(v_ref_3361_, v_msg_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
    crate::leanh::lean_dec(v___y_3366_);
    crate::leanh::lean_dec_ref(v___y_3365_);
    crate::leanh::lean_dec(v___y_3364_);
    crate::leanh::lean_dec_ref(v___y_3363_);
    crate::leanh::lean_dec(v_ref_3361_);
    return v_res_3368_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(
    mut v_ref_3369_: *mut crate::leanh::LeanObject,
    mut v_msg_3370_: *mut crate::leanh::LeanObject,
    mut v_declHint_3371_: *mut crate::leanh::LeanObject,
    mut v___y_3372_: *mut crate::leanh::LeanObject,
    mut v___y_3373_: *mut crate::leanh::LeanObject,
    mut v___y_3374_: *mut crate::leanh::LeanObject,
    mut v___y_3375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3377_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(v_msg_3370_, v_declHint_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
    v_a_3378_ = crate::leanh::lean_ctor_get(v___x_3377_, 0);
    crate::leanh::lean_inc(v_a_3378_);
    crate::leanh::lean_dec_ref(v___x_3377_);
    v___x_3379_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(v_ref_3369_, v_a_3378_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
    return v___x_3379_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg___boxed(
    mut v_ref_3380_: *mut crate::leanh::LeanObject,
    mut v_msg_3381_: *mut crate::leanh::LeanObject,
    mut v_declHint_3382_: *mut crate::leanh::LeanObject,
    mut v___y_3383_: *mut crate::leanh::LeanObject,
    mut v___y_3384_: *mut crate::leanh::LeanObject,
    mut v___y_3385_: *mut crate::leanh::LeanObject,
    mut v___y_3386_: *mut crate::leanh::LeanObject,
    mut v___y_3387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3388_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(v_ref_3380_, v_msg_3381_, v_declHint_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_);
    crate::leanh::lean_dec(v___y_3386_);
    crate::leanh::lean_dec_ref(v___y_3385_);
    crate::leanh::lean_dec(v___y_3384_);
    crate::leanh::lean_dec_ref(v___y_3383_);
    crate::leanh::lean_dec(v_ref_3380_);
    return v_res_3388_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3390_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0;
    v___x_3391_ = l_Lean_stringToMessageData(v___x_3390_);
    return v___x_3391_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(
    mut v_ref_3392_: *mut crate::leanh::LeanObject,
    mut v_constName_3393_: *mut crate::leanh::LeanObject,
    mut v___y_3394_: *mut crate::leanh::LeanObject,
    mut v___y_3395_: *mut crate::leanh::LeanObject,
    mut v___y_3396_: *mut crate::leanh::LeanObject,
    mut v___y_3397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: u8 = 0;
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3399_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1);
    v___x_3400_ = 0;
    crate::leanh::lean_inc(v_constName_3393_);
    v___x_3401_ = l_Lean_MessageData_ofConstName(v_constName_3393_, v___x_3400_);
    v___x_3402_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3402_, 0, v___x_3399_);
    crate::leanh::lean_ctor_set(v___x_3402_, 1, v___x_3401_);
    v___x_3403_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1_once
        ),
        _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1,
    );
    v___x_3404_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3404_, 0, v___x_3402_);
    crate::leanh::lean_ctor_set(v___x_3404_, 1, v___x_3403_);
    v___x_3405_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(v_ref_3392_, v___x_3404_, v_constName_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
    return v___x_3405_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___boxed(
    mut v_ref_3406_: *mut crate::leanh::LeanObject,
    mut v_constName_3407_: *mut crate::leanh::LeanObject,
    mut v___y_3408_: *mut crate::leanh::LeanObject,
    mut v___y_3409_: *mut crate::leanh::LeanObject,
    mut v___y_3410_: *mut crate::leanh::LeanObject,
    mut v___y_3411_: *mut crate::leanh::LeanObject,
    mut v___y_3412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3413_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_3406_, v_constName_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
    crate::leanh::lean_dec(v___y_3411_);
    crate::leanh::lean_dec_ref(v___y_3410_);
    crate::leanh::lean_dec(v___y_3409_);
    crate::leanh::lean_dec_ref(v___y_3408_);
    crate::leanh::lean_dec(v_ref_3406_);
    return v_res_3413_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(
    mut v_constName_3414_: *mut crate::leanh::LeanObject,
    mut v___y_3415_: *mut crate::leanh::LeanObject,
    mut v___y_3416_: *mut crate::leanh::LeanObject,
    mut v___y_3417_: *mut crate::leanh::LeanObject,
    mut v___y_3418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_3420_ = crate::leanh::lean_ctor_get(v___y_3417_, 5);
    v___x_3421_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_3420_, v_constName_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
    return v___x_3421_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg___boxed(
    mut v_constName_3422_: *mut crate::leanh::LeanObject,
    mut v___y_3423_: *mut crate::leanh::LeanObject,
    mut v___y_3424_: *mut crate::leanh::LeanObject,
    mut v___y_3425_: *mut crate::leanh::LeanObject,
    mut v___y_3426_: *mut crate::leanh::LeanObject,
    mut v___y_3427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3428_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(v_constName_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
    crate::leanh::lean_dec(v___y_3426_);
    crate::leanh::lean_dec_ref(v___y_3425_);
    crate::leanh::lean_dec(v___y_3424_);
    crate::leanh::lean_dec_ref(v___y_3423_);
    return v_res_3428_;
}
pub unsafe fn l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(
    mut v_constName_3429_: *mut crate::leanh::LeanObject,
    mut v___y_3430_: *mut crate::leanh::LeanObject,
    mut v___y_3431_: *mut crate::leanh::LeanObject,
    mut v___y_3432_: *mut crate::leanh::LeanObject,
    mut v___y_3433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: u8 = 0;
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3443_: u8 = 0;
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3447_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3435_ = lean_st_ref_get(v___y_3433_);
                v_env_3436_ = crate::leanh::lean_ctor_get(v___x_3435_, 0);
                crate::leanh::lean_inc_ref(v_env_3436_);
                crate::leanh::lean_dec(v___x_3435_);
                v___x_3437_ = 0;
                crate::leanh::lean_inc(v_constName_3429_);
                v___x_3438_ =
                    l_Lean_Environment_find_x3f(v_env_3436_, v_constName_3429_, v___x_3437_);
                if crate::leanh::lean_obj_tag(v___x_3438_) == 0 {
                    v___x_3439_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(v_constName_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_);
                    return v___x_3439_;
                } else {
                    crate::leanh::lean_dec(v_constName_3429_);
                    v_val_3440_ = crate::leanh::lean_ctor_get(v___x_3438_, 0);
                    v_isSharedCheck_3447_ = (!crate::leanh::lean_is_exclusive(v___x_3438_)) as u8;
                    if v_isSharedCheck_3447_ == 0 {
                        v___x_3442_ = v___x_3438_;
                        v_isShared_3443_ = v_isSharedCheck_3447_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3440_);
                        crate::leanh::lean_dec(v___x_3438_);
                        v___x_3442_ = crate::leanh::lean_box(0);
                        v_isShared_3443_ = v_isSharedCheck_3447_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3443_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3442_, 0);
                    v___x_3445_ = v___x_3442_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3446_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_val_3440_);
                    v___x_3445_ = v_reuseFailAlloc_3446_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3445_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00mkCtorIdx_spec__2___boxed(
    mut v_constName_3448_: *mut crate::leanh::LeanObject,
    mut v___y_3449_: *mut crate::leanh::LeanObject,
    mut v___y_3450_: *mut crate::leanh::LeanObject,
    mut v___y_3451_: *mut crate::leanh::LeanObject,
    mut v___y_3452_: *mut crate::leanh::LeanObject,
    mut v___y_3453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3454_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(
        v_constName_3448_,
        v___y_3449_,
        v___y_3450_,
        v___y_3451_,
        v___y_3452_,
    );
    crate::leanh::lean_dec(v___y_3452_);
    crate::leanh::lean_dec_ref(v___y_3451_);
    crate::leanh::lean_dec(v___y_3450_);
    crate::leanh::lean_dec_ref(v___y_3449_);
    return v_res_3454_;
}
pub unsafe fn l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13(
    mut v___x_3455_: u8,
    mut v_x_3456_: *mut crate::leanh::LeanObject,
    mut v___y_3457_: *mut crate::leanh::LeanObject,
    mut v___y_3458_: *mut crate::leanh::LeanObject,
    mut v___y_3459_: *mut crate::leanh::LeanObject,
    mut v___y_3460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3462_: u8 = 0;
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3471_: u8 = 0;
    let mut v___y_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3474_: u8 = 0;
    let mut v_val_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: u8 = 0;
    let mut v___x_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3488_: u8 = 0;
    let mut v_a_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3492_: u8 = 0;
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3496_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3456_) == 0 {
                    v___x_3462_ = 1;
                    v___x_3463_ = crate::leanh::lean_box((v___x_3462_) as usize);
                    v___x_3464_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3464_, 0, v___x_3463_);
                    return v___x_3464_;
                } else {
                    v_head_3465_ = crate::leanh::lean_ctor_get(v_x_3456_, 0);
                    crate::leanh::lean_inc(v_head_3465_);
                    v_tail_3466_ = crate::leanh::lean_ctor_get(v_x_3456_, 1);
                    crate::leanh::lean_inc(v_tail_3466_);
                    crate::leanh::lean_dec_ref_known(v_x_3456_, 2);
                    v___x_3467_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(
                        v_head_3465_,
                        v___y_3457_,
                        v___y_3458_,
                        v___y_3459_,
                        v___y_3460_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3467_) == 0 {
                        v_a_3468_ = crate::leanh::lean_ctor_get(v___x_3467_, 0);
                        v_isSharedCheck_3488_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3467_)) as u8;
                        if v_isSharedCheck_3488_ == 0 {
                            v___x_3470_ = v___x_3467_;
                            v_isShared_3471_ = v_isSharedCheck_3488_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3468_);
                            crate::leanh::lean_dec(v___x_3467_);
                            v___x_3470_ = crate::leanh::lean_box(0);
                            v_isShared_3471_ = v_isSharedCheck_3488_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_tail_3466_);
                        v_a_3489_ = crate::leanh::lean_ctor_get(v___x_3467_, 0);
                        v_isSharedCheck_3496_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3467_)) as u8;
                        if v_isSharedCheck_3496_ == 0 {
                            v___x_3491_ = v___x_3467_;
                            v_isShared_3492_ = v_isSharedCheck_3496_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3489_);
                            crate::leanh::lean_dec(v___x_3467_);
                            v___x_3491_ = crate::leanh::lean_box(0);
                            v_isShared_3492_ = v_isSharedCheck_3496_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3468_) == 6 {
                    v_val_3476_ = crate::leanh::lean_ctor_get(v_a_3468_, 0);
                    crate::leanh::lean_inc_ref(v_val_3476_);
                    crate::leanh::lean_dec_ref_known(v_a_3468_, 1);
                    v_numFields_3477_ = crate::leanh::lean_ctor_get(v_val_3476_, 4);
                    crate::leanh::lean_inc(v_numFields_3477_);
                    crate::leanh::lean_dec_ref(v_val_3476_);
                    v___x_3478_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3479_ = lean_nat_dec_eq(v_numFields_3477_, v___x_3478_);
                    crate::leanh::lean_dec(v_numFields_3477_);
                    v___x_3480_ = crate::leanh::lean_box((v___x_3479_) as usize);
                    if v_isShared_3471_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3470_, 0, v___x_3480_);
                        v___x_3482_ = v___x_3470_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3483_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3483_, 0, v___x_3480_);
                        v___x_3482_ = v_reuseFailAlloc_3483_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3468_);
                    v___x_3484_ = crate::leanh::lean_box((v___x_3455_) as usize);
                    if v_isShared_3471_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3470_, 0, v___x_3484_);
                        v___x_3486_ = v___x_3470_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3487_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3484_);
                        v___x_3486_ = v_reuseFailAlloc_3487_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_a_3474_ == 0 {
                    crate::leanh::lean_dec(v_tail_3466_);
                    return v___y_3473_;
                } else {
                    crate::leanh::lean_dec_ref(v___y_3473_);
                    v_x_3456_ = v_tail_3466_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                v___y_3473_ = v___x_3482_;
                v_a_3474_ = v___x_3479_;
                state = 2;
                continue;
            }
            4 => {
                v___y_3473_ = v___x_3486_;
                v_a_3474_ = v___x_3455_;
                state = 2;
                continue;
            }
            5 => {
                if v_isShared_3492_ == 0 {
                    v___x_3494_ = v___x_3491_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3495_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_a_3489_);
                    v___x_3494_ = v_reuseFailAlloc_3495_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3494_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13___boxed(
    mut v___x_3497_: *mut crate::leanh::LeanObject,
    mut v_x_3498_: *mut crate::leanh::LeanObject,
    mut v___y_3499_: *mut crate::leanh::LeanObject,
    mut v___y_3500_: *mut crate::leanh::LeanObject,
    mut v___y_3501_: *mut crate::leanh::LeanObject,
    mut v___y_3502_: *mut crate::leanh::LeanObject,
    mut v___y_3503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_35476__boxed_3504_: u8 = 0;
    let mut v_res_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_35476__boxed_3504_ = (crate::leanh::lean_unbox(v___x_3497_) as u8);
    v_res_3505_ = l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13(
        v___x_35476__boxed_3504_,
        v_x_3498_,
        v___y_3499_,
        v___y_3500_,
        v___y_3501_,
        v___y_3502_,
    );
    crate::leanh::lean_dec(v___y_3502_);
    crate::leanh::lean_dec_ref(v___y_3501_);
    crate::leanh::lean_dec(v___y_3500_);
    crate::leanh::lean_dec_ref(v___y_3499_);
    return v_res_3505_;
}
pub unsafe fn l_Lean_isEnumType___at___00mkCtorIdx_spec__9(
    mut v_declName_3506_: *mut crate::leanh::LeanObject,
    mut v___y_3507_: *mut crate::leanh::LeanObject,
    mut v___y_3508_: *mut crate::leanh::LeanObject,
    mut v___y_3509_: *mut crate::leanh::LeanObject,
    mut v___y_3510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3516_: u8 = 0;
    let mut v_val_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isRec_3522_: u8 = 0;
    let mut v_isUnsafe_3523_: u8 = 0;
    let mut v_type_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: u8 = 0;
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: u8 = 0;
    let mut v___x_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: u8 = 0;
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: u8 = 0;
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: u8 = 0;
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: u8 = 0;
    let mut v___x_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: u8 = 0;
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3568_: u8 = 0;
    let mut v_a_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3572_: u8 = 0;
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3576_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3512_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(
                    v_declName_3506_,
                    v___y_3507_,
                    v___y_3508_,
                    v___y_3509_,
                    v___y_3510_,
                );
                if crate::leanh::lean_obj_tag(v___x_3512_) == 0 {
                    v_a_3513_ = crate::leanh::lean_ctor_get(v___x_3512_, 0);
                    v_isSharedCheck_3568_ = (!crate::leanh::lean_is_exclusive(v___x_3512_)) as u8;
                    if v_isSharedCheck_3568_ == 0 {
                        v___x_3515_ = v___x_3512_;
                        v_isShared_3516_ = v_isSharedCheck_3568_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3513_);
                        crate::leanh::lean_dec(v___x_3512_);
                        v___x_3515_ = crate::leanh::lean_box(0);
                        v_isShared_3516_ = v_isSharedCheck_3568_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3569_ = crate::leanh::lean_ctor_get(v___x_3512_, 0);
                    v_isSharedCheck_3576_ = (!crate::leanh::lean_is_exclusive(v___x_3512_)) as u8;
                    if v_isSharedCheck_3576_ == 0 {
                        v___x_3571_ = v___x_3512_;
                        v_isShared_3572_ = v_isSharedCheck_3576_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3569_);
                        crate::leanh::lean_dec(v___x_3512_);
                        v___x_3571_ = crate::leanh::lean_box(0);
                        v_isShared_3572_ = v_isSharedCheck_3576_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3513_) == 5 {
                    v_val_3517_ = crate::leanh::lean_ctor_get(v_a_3513_, 0);
                    crate::leanh::lean_inc_ref(v_val_3517_);
                    crate::leanh::lean_dec_ref_known(v_a_3513_, 1);
                    v_toConstantVal_3518_ = crate::leanh::lean_ctor_get(v_val_3517_, 0);
                    v_numParams_3519_ = crate::leanh::lean_ctor_get(v_val_3517_, 1);
                    crate::leanh::lean_inc(v_numParams_3519_);
                    v_numIndices_3520_ = crate::leanh::lean_ctor_get(v_val_3517_, 2);
                    crate::leanh::lean_inc(v_numIndices_3520_);
                    v_ctors_3521_ = crate::leanh::lean_ctor_get(v_val_3517_, 4);
                    crate::leanh::lean_inc(v_ctors_3521_);
                    v_isRec_3522_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_3517_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6) as u32,
                    );
                    v_isUnsafe_3523_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_3517_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 6 + 1) as u32,
                    );
                    v_type_3524_ = crate::leanh::lean_ctor_get(v_toConstantVal_3518_, 2);
                    v___x_3525_ = l_Lean_Expr_isProp(v_type_3524_);
                    if v___x_3525_ == 0 {
                        v___x_3526_ = l_Lean_InductiveVal_numTypeFormers(v_val_3517_);
                        crate::leanh::lean_dec_ref(v_val_3517_);
                        v___x_3527_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3528_ = lean_nat_dec_eq(v___x_3526_, v___x_3527_);
                        crate::leanh::lean_dec(v___x_3526_);
                        if v___x_3528_ == 0 {
                            crate::leanh::lean_dec(v_ctors_3521_);
                            crate::leanh::lean_dec(v_numIndices_3520_);
                            crate::leanh::lean_dec(v_numParams_3519_);
                            v___x_3529_ = crate::leanh::lean_box((v___x_3528_) as usize);
                            if v_isShared_3516_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3515_, 0, v___x_3529_);
                                v___x_3531_ = v___x_3515_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_3532_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3529_);
                                v___x_3531_ = v_reuseFailAlloc_3532_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_3533_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_3534_ = lean_nat_dec_eq(v_numIndices_3520_, v___x_3533_);
                            crate::leanh::lean_dec(v_numIndices_3520_);
                            if v___x_3534_ == 0 {
                                crate::leanh::lean_dec(v_ctors_3521_);
                                crate::leanh::lean_dec(v_numParams_3519_);
                                v___x_3535_ = crate::leanh::lean_box((v___x_3534_) as usize);
                                if v_isShared_3516_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3515_, 0, v___x_3535_);
                                    v___x_3537_ = v___x_3515_;
                                    state = 3;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3538_ =
                                        crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3538_,
                                        0,
                                        v___x_3535_,
                                    );
                                    v___x_3537_ = v_reuseFailAlloc_3538_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                v___x_3539_ = lean_nat_dec_eq(v_numParams_3519_, v___x_3533_);
                                crate::leanh::lean_dec(v_numParams_3519_);
                                if v___x_3539_ == 0 {
                                    crate::leanh::lean_dec(v_ctors_3521_);
                                    v___x_3540_ = crate::leanh::lean_box((v___x_3539_) as usize);
                                    if v_isShared_3516_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_3515_, 0, v___x_3540_);
                                        v___x_3542_ = v___x_3515_;
                                        state = 4;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3543_ =
                                            crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3543_,
                                            0,
                                            v___x_3540_,
                                        );
                                        v___x_3542_ = v_reuseFailAlloc_3543_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    v___x_3544_ = l_List_isEmpty___redArg(v_ctors_3521_);
                                    if v___x_3544_ == 0 {
                                        if v_isRec_3522_ == 0 {
                                            if v_isUnsafe_3523_ == 0 {
                                                crate::leanh::lean_del_object(v___x_3515_);
                                                v___x_3545_ = l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13(v_isUnsafe_3523_, v_ctors_3521_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
                                                return v___x_3545_;
                                            } else {
                                                crate::leanh::lean_dec(v_ctors_3521_);
                                                v___x_3546_ = crate::leanh::lean_box(
                                                    (v_isRec_3522_) as usize,
                                                );
                                                if v_isShared_3516_ == 0 {
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_3515_,
                                                        0,
                                                        v___x_3546_,
                                                    );
                                                    v___x_3548_ = v___x_3515_;
                                                    state = 5;
                                                    continue;
                                                } else {
                                                    v_reuseFailAlloc_3549_ =
                                                        crate::leanh::lean_alloc_ctor(
                                                            0,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                    crate::leanh::lean_ctor_set(
                                                        v_reuseFailAlloc_3549_,
                                                        0,
                                                        v___x_3546_,
                                                    );
                                                    v___x_3548_ = v_reuseFailAlloc_3549_;
                                                    state = 5;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_ctors_3521_);
                                            v___x_3550_ =
                                                crate::leanh::lean_box((v___x_3544_) as usize);
                                            if v_isShared_3516_ == 0 {
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3515_,
                                                    0,
                                                    v___x_3550_,
                                                );
                                                v___x_3552_ = v___x_3515_;
                                                state = 6;
                                                continue;
                                            } else {
                                                v_reuseFailAlloc_3553_ =
                                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v_reuseFailAlloc_3553_,
                                                    0,
                                                    v___x_3550_,
                                                );
                                                v___x_3552_ = v_reuseFailAlloc_3553_;
                                                state = 6;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_ctors_3521_);
                                        v___x_3554_ =
                                            crate::leanh::lean_box((v___x_3525_) as usize);
                                        if v_isShared_3516_ == 0 {
                                            crate::leanh::lean_ctor_set(
                                                v___x_3515_,
                                                0,
                                                v___x_3554_,
                                            );
                                            v___x_3556_ = v___x_3515_;
                                            state = 7;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_3557_ =
                                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3557_,
                                                0,
                                                v___x_3554_,
                                            );
                                            v___x_3556_ = v_reuseFailAlloc_3557_;
                                            state = 7;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_ctors_3521_);
                        crate::leanh::lean_dec(v_numIndices_3520_);
                        crate::leanh::lean_dec(v_numParams_3519_);
                        crate::leanh::lean_dec_ref(v_val_3517_);
                        v___x_3558_ = 0;
                        v___x_3559_ = crate::leanh::lean_box((v___x_3558_) as usize);
                        if v_isShared_3516_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3515_, 0, v___x_3559_);
                            v___x_3561_ = v___x_3515_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_3562_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3562_, 0, v___x_3559_);
                            v___x_3561_ = v_reuseFailAlloc_3562_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3513_);
                    v___x_3563_ = 0;
                    v___x_3564_ = crate::leanh::lean_box((v___x_3563_) as usize);
                    if v_isShared_3516_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3515_, 0, v___x_3564_);
                        v___x_3566_ = v___x_3515_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3567_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3567_, 0, v___x_3564_);
                        v___x_3566_ = v_reuseFailAlloc_3567_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3531_;
            }
            3 => {
                return v___x_3537_;
            }
            4 => {
                return v___x_3542_;
            }
            5 => {
                return v___x_3548_;
            }
            6 => {
                return v___x_3552_;
            }
            7 => {
                return v___x_3556_;
            }
            8 => {
                return v___x_3561_;
            }
            9 => {
                return v___x_3566_;
            }
            10 => {
                if v_isShared_3572_ == 0 {
                    v___x_3574_ = v___x_3571_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3575_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
                    v___x_3574_ = v_reuseFailAlloc_3575_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3574_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_isEnumType___at___00mkCtorIdx_spec__9___boxed(
    mut v_declName_3577_: *mut crate::leanh::LeanObject,
    mut v___y_3578_: *mut crate::leanh::LeanObject,
    mut v___y_3579_: *mut crate::leanh::LeanObject,
    mut v___y_3580_: *mut crate::leanh::LeanObject,
    mut v___y_3581_: *mut crate::leanh::LeanObject,
    mut v___y_3582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3583_ = l_Lean_isEnumType___at___00mkCtorIdx_spec__9(
        v_declName_3577_,
        v___y_3578_,
        v___y_3579_,
        v___y_3580_,
        v___y_3581_,
    );
    crate::leanh::lean_dec(v___y_3581_);
    crate::leanh::lean_dec_ref(v___y_3580_);
    crate::leanh::lean_dec(v___y_3579_);
    crate::leanh::lean_dec_ref(v___y_3578_);
    return v_res_3583_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0(
    mut v_k_3584_: *mut crate::leanh::LeanObject,
    mut v_b_3585_: *mut crate::leanh::LeanObject,
    mut v___y_3586_: *mut crate::leanh::LeanObject,
    mut v___y_3587_: *mut crate::leanh::LeanObject,
    mut v___y_3588_: *mut crate::leanh::LeanObject,
    mut v___y_3589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_3589_);
    crate::leanh::lean_inc_ref(v___y_3588_);
    crate::leanh::lean_inc(v___y_3587_);
    crate::leanh::lean_inc_ref(v___y_3586_);
    v___x_3591_ = crate::leanh::lean_apply_6(
        v_k_3584_,
        v_b_3585_,
        v___y_3586_,
        v___y_3587_,
        v___y_3588_,
        v___y_3589_,
        crate::leanh::lean_box(0),
    );
    return v___x_3591_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed(
    mut v_k_3592_: *mut crate::leanh::LeanObject,
    mut v_b_3593_: *mut crate::leanh::LeanObject,
    mut v___y_3594_: *mut crate::leanh::LeanObject,
    mut v___y_3595_: *mut crate::leanh::LeanObject,
    mut v___y_3596_: *mut crate::leanh::LeanObject,
    mut v___y_3597_: *mut crate::leanh::LeanObject,
    mut v___y_3598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3599_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0(v_k_3592_, v_b_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
    crate::leanh::lean_dec(v___y_3597_);
    crate::leanh::lean_dec_ref(v___y_3596_);
    crate::leanh::lean_dec(v___y_3595_);
    crate::leanh::lean_dec_ref(v___y_3594_);
    return v_res_3599_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(
    mut v_name_3600_: *mut crate::leanh::LeanObject,
    mut v_bi_3601_: u8,
    mut v_type_3602_: *mut crate::leanh::LeanObject,
    mut v_k_3603_: *mut crate::leanh::LeanObject,
    mut v_kind_3604_: u8,
    mut v___y_3605_: *mut crate::leanh::LeanObject,
    mut v___y_3606_: *mut crate::leanh::LeanObject,
    mut v___y_3607_: *mut crate::leanh::LeanObject,
    mut v___y_3608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3615_: u8 = 0;
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3619_: u8 = 0;
    let mut v_a_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3623_: u8 = 0;
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3627_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3610_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                crate::leanh::lean_closure_set(v___f_3610_, 0, v_k_3603_);
                v___x_3611_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_3600_,
                    v_bi_3601_,
                    v_type_3602_,
                    v___f_3610_,
                    v_kind_3604_,
                    v___y_3605_,
                    v___y_3606_,
                    v___y_3607_,
                    v___y_3608_,
                );
                if crate::leanh::lean_obj_tag(v___x_3611_) == 0 {
                    v_a_3612_ = crate::leanh::lean_ctor_get(v___x_3611_, 0);
                    v_isSharedCheck_3619_ = (!crate::leanh::lean_is_exclusive(v___x_3611_)) as u8;
                    if v_isSharedCheck_3619_ == 0 {
                        v___x_3614_ = v___x_3611_;
                        v_isShared_3615_ = v_isSharedCheck_3619_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3612_);
                        crate::leanh::lean_dec(v___x_3611_);
                        v___x_3614_ = crate::leanh::lean_box(0);
                        v_isShared_3615_ = v_isSharedCheck_3619_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3620_ = crate::leanh::lean_ctor_get(v___x_3611_, 0);
                    v_isSharedCheck_3627_ = (!crate::leanh::lean_is_exclusive(v___x_3611_)) as u8;
                    if v_isSharedCheck_3627_ == 0 {
                        v___x_3622_ = v___x_3611_;
                        v_isShared_3623_ = v_isSharedCheck_3627_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3620_);
                        crate::leanh::lean_dec(v___x_3611_);
                        v___x_3622_ = crate::leanh::lean_box(0);
                        v_isShared_3623_ = v_isSharedCheck_3627_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3615_ == 0 {
                    v___x_3617_ = v___x_3614_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3618_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3612_);
                    v___x_3617_ = v_reuseFailAlloc_3618_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3617_;
            }
            3 => {
                if v_isShared_3623_ == 0 {
                    v___x_3625_ = v___x_3622_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3626_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_a_3620_);
                    v___x_3625_ = v_reuseFailAlloc_3626_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3625_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___boxed(
    mut v_name_3628_: *mut crate::leanh::LeanObject,
    mut v_bi_3629_: *mut crate::leanh::LeanObject,
    mut v_type_3630_: *mut crate::leanh::LeanObject,
    mut v_k_3631_: *mut crate::leanh::LeanObject,
    mut v_kind_3632_: *mut crate::leanh::LeanObject,
    mut v___y_3633_: *mut crate::leanh::LeanObject,
    mut v___y_3634_: *mut crate::leanh::LeanObject,
    mut v___y_3635_: *mut crate::leanh::LeanObject,
    mut v___y_3636_: *mut crate::leanh::LeanObject,
    mut v___y_3637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_3638_: u8 = 0;
    let mut v_kind_boxed_3639_: u8 = 0;
    let mut v_res_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_3638_ = (crate::leanh::lean_unbox(v_bi_3629_) as u8);
    v_kind_boxed_3639_ = (crate::leanh::lean_unbox(v_kind_3632_) as u8);
    v_res_3640_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(v_name_3628_, v_bi_boxed_3638_, v_type_3630_, v_k_3631_, v_kind_boxed_3639_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_);
    crate::leanh::lean_dec(v___y_3636_);
    crate::leanh::lean_dec_ref(v___y_3635_);
    crate::leanh::lean_dec(v___y_3634_);
    crate::leanh::lean_dec_ref(v___y_3633_);
    return v_res_3640_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg(
    mut v_name_3641_: *mut crate::leanh::LeanObject,
    mut v_type_3642_: *mut crate::leanh::LeanObject,
    mut v_k_3643_: *mut crate::leanh::LeanObject,
    mut v___y_3644_: *mut crate::leanh::LeanObject,
    mut v___y_3645_: *mut crate::leanh::LeanObject,
    mut v___y_3646_: *mut crate::leanh::LeanObject,
    mut v___y_3647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3649_: u8 = 0;
    let mut v___x_3650_: u8 = 0;
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3649_ = 0;
    v___x_3650_ = 0;
    v___x_3651_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(v_name_3641_, v___x_3649_, v_type_3642_, v_k_3643_, v___x_3650_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
    return v___x_3651_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg___boxed(
    mut v_name_3652_: *mut crate::leanh::LeanObject,
    mut v_type_3653_: *mut crate::leanh::LeanObject,
    mut v_k_3654_: *mut crate::leanh::LeanObject,
    mut v___y_3655_: *mut crate::leanh::LeanObject,
    mut v___y_3656_: *mut crate::leanh::LeanObject,
    mut v___y_3657_: *mut crate::leanh::LeanObject,
    mut v___y_3658_: *mut crate::leanh::LeanObject,
    mut v___y_3659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3660_ = l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg(
        v_name_3652_,
        v_type_3653_,
        v_k_3654_,
        v___y_3655_,
        v___y_3656_,
        v___y_3657_,
        v___y_3658_,
    );
    crate::leanh::lean_dec(v___y_3658_);
    crate::leanh::lean_dec_ref(v___y_3657_);
    crate::leanh::lean_dec(v___y_3656_);
    crate::leanh::lean_dec_ref(v___y_3655_);
    return v_res_3660_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(
    mut v_env_3661_: *mut crate::leanh::LeanObject,
    mut v___y_3662_: *mut crate::leanh::LeanObject,
    mut v___y_3663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3675_: u8 = 0;
    let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3687_: u8 = 0;
    let mut v___x_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3695_: u8 = 0;
    let mut v_unused_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3698_: u8 = 0;
    let mut v_unused_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3665_ = lean_st_ref_take(v___y_3663_);
                v_nextMacroScope_3666_ = crate::leanh::lean_ctor_get(v___x_3665_, 1);
                v_ngen_3667_ = crate::leanh::lean_ctor_get(v___x_3665_, 2);
                v_auxDeclNGen_3668_ = crate::leanh::lean_ctor_get(v___x_3665_, 3);
                v_traceState_3669_ = crate::leanh::lean_ctor_get(v___x_3665_, 4);
                v_messages_3670_ = crate::leanh::lean_ctor_get(v___x_3665_, 6);
                v_infoState_3671_ = crate::leanh::lean_ctor_get(v___x_3665_, 7);
                v_snapshotTasks_3672_ = crate::leanh::lean_ctor_get(v___x_3665_, 8);
                v_isSharedCheck_3698_ = (!crate::leanh::lean_is_exclusive(v___x_3665_)) as u8;
                if v_isSharedCheck_3698_ == 0 {
                    v_unused_3699_ = crate::leanh::lean_ctor_get(v___x_3665_, 5);
                    crate::leanh::lean_dec(v_unused_3699_);
                    v_unused_3700_ = crate::leanh::lean_ctor_get(v___x_3665_, 0);
                    crate::leanh::lean_dec(v_unused_3700_);
                    v___x_3674_ = v___x_3665_;
                    v_isShared_3675_ = v_isSharedCheck_3698_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3672_);
                    crate::leanh::lean_inc(v_infoState_3671_);
                    crate::leanh::lean_inc(v_messages_3670_);
                    crate::leanh::lean_inc(v_traceState_3669_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3668_);
                    crate::leanh::lean_inc(v_ngen_3667_);
                    crate::leanh::lean_inc(v_nextMacroScope_3666_);
                    crate::leanh::lean_dec(v___x_3665_);
                    v___x_3674_ = crate::leanh::lean_box(0);
                    v_isShared_3675_ = v_isSharedCheck_3698_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3676_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once
                    ),
                    _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2,
                );
                if v_isShared_3675_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3674_, 5, v___x_3676_);
                    crate::leanh::lean_ctor_set(v___x_3674_, 0, v_env_3661_);
                    v___x_3678_ = v___x_3674_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3697_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_env_3661_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3697_, 1, v_nextMacroScope_3666_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3697_, 2, v_ngen_3667_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3697_, 3, v_auxDeclNGen_3668_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3697_, 4, v_traceState_3669_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3697_, 5, v___x_3676_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3697_, 6, v_messages_3670_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3697_, 7, v_infoState_3671_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3697_, 8, v_snapshotTasks_3672_);
                    v___x_3678_ = v_reuseFailAlloc_3697_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3679_ = lean_st_ref_set(v___y_3663_, v___x_3678_);
                v___x_3680_ = lean_st_ref_take(v___y_3662_);
                v_mctx_3681_ = crate::leanh::lean_ctor_get(v___x_3680_, 0);
                v_zetaDeltaFVarIds_3682_ = crate::leanh::lean_ctor_get(v___x_3680_, 2);
                v_postponed_3683_ = crate::leanh::lean_ctor_get(v___x_3680_, 3);
                v_diag_3684_ = crate::leanh::lean_ctor_get(v___x_3680_, 4);
                v_isSharedCheck_3695_ = (!crate::leanh::lean_is_exclusive(v___x_3680_)) as u8;
                if v_isSharedCheck_3695_ == 0 {
                    v_unused_3696_ = crate::leanh::lean_ctor_get(v___x_3680_, 1);
                    crate::leanh::lean_dec(v_unused_3696_);
                    v___x_3686_ = v___x_3680_;
                    v_isShared_3687_ = v_isSharedCheck_3695_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_3684_);
                    crate::leanh::lean_inc(v_postponed_3683_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_3682_);
                    crate::leanh::lean_inc(v_mctx_3681_);
                    crate::leanh::lean_dec(v___x_3680_);
                    v___x_3686_ = crate::leanh::lean_box(0);
                    v_isShared_3687_ = v_isSharedCheck_3695_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3688_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once
                    ),
                    _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3,
                );
                if v_isShared_3687_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3686_, 1, v___x_3688_);
                    v___x_3690_ = v___x_3686_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3694_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_mctx_3681_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3694_, 1, v___x_3688_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3694_,
                        2,
                        v_zetaDeltaFVarIds_3682_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3694_, 3, v_postponed_3683_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3694_, 4, v_diag_3684_);
                    v___x_3690_ = v_reuseFailAlloc_3694_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3691_ = lean_st_ref_set(v___y_3662_, v___x_3690_);
                v___x_3692_ = crate::leanh::lean_box(0);
                v___x_3693_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3693_, 0, v___x_3692_);
                return v___x_3693_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg___boxed(
    mut v_env_3701_: *mut crate::leanh::LeanObject,
    mut v___y_3702_: *mut crate::leanh::LeanObject,
    mut v___y_3703_: *mut crate::leanh::LeanObject,
    mut v___y_3704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3705_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(v_env_3701_, v___y_3702_, v___y_3703_);
    crate::leanh::lean_dec(v___y_3703_);
    crate::leanh::lean_dec(v___y_3702_);
    return v_res_3705_;
}
pub unsafe fn l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11(
    mut v_declName_3706_: *mut crate::leanh::LeanObject,
    mut v_entry_3707_: *mut crate::leanh::LeanObject,
    mut v___y_3708_: *mut crate::leanh::LeanObject,
    mut v___y_3709_: *mut crate::leanh::LeanObject,
    mut v___y_3710_: *mut crate::leanh::LeanObject,
    mut v___y_3711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3720_: u8 = 0;
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3726_: u8 = 0;
    let mut v_a_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3713_ = lean_st_ref_get(v___y_3711_);
                v_env_3714_ = crate::leanh::lean_ctor_get(v___x_3713_, 0);
                crate::leanh::lean_inc_ref(v_env_3714_);
                crate::leanh::lean_dec(v___x_3713_);
                v___x_3715_ = l_Lean_Linter_deprecatedAttr;
                v___x_3716_ = l_Lean_ParametricAttribute_setParam___redArg(
                    v___x_3715_,
                    v_env_3714_,
                    v_declName_3706_,
                    v_entry_3707_,
                );
                if crate::leanh::lean_obj_tag(v___x_3716_) == 0 {
                    v_a_3717_ = crate::leanh::lean_ctor_get(v___x_3716_, 0);
                    v_isSharedCheck_3726_ = (!crate::leanh::lean_is_exclusive(v___x_3716_)) as u8;
                    if v_isSharedCheck_3726_ == 0 {
                        v___x_3719_ = v___x_3716_;
                        v_isShared_3720_ = v_isSharedCheck_3726_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3717_);
                        crate::leanh::lean_dec(v___x_3716_);
                        v___x_3719_ = crate::leanh::lean_box(0);
                        v_isShared_3720_ = v_isSharedCheck_3726_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3727_ = crate::leanh::lean_ctor_get(v___x_3716_, 0);
                    crate::leanh::lean_inc(v_a_3727_);
                    crate::leanh::lean_dec_ref_known(v___x_3716_, 1);
                    v___x_3728_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(v_a_3727_, v___y_3709_, v___y_3711_);
                    return v___x_3728_;
                }
            }
            1 => {
                if v_isShared_3720_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3719_, 3);
                    v___x_3722_ = v___x_3719_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3725_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3725_, 0, v_a_3717_);
                    v___x_3722_ = v_reuseFailAlloc_3725_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3723_ = l_Lean_MessageData_ofFormat(v___x_3722_);
                v___x_3724_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v___x_3723_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
                return v___x_3724_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11___boxed(
    mut v_declName_3729_: *mut crate::leanh::LeanObject,
    mut v_entry_3730_: *mut crate::leanh::LeanObject,
    mut v___y_3731_: *mut crate::leanh::LeanObject,
    mut v___y_3732_: *mut crate::leanh::LeanObject,
    mut v___y_3733_: *mut crate::leanh::LeanObject,
    mut v___y_3734_: *mut crate::leanh::LeanObject,
    mut v___y_3735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3736_ = l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11(
        v_declName_3729_,
        v_entry_3730_,
        v___y_3731_,
        v___y_3732_,
        v___y_3733_,
        v___y_3734_,
    );
    crate::leanh::lean_dec(v___y_3734_);
    crate::leanh::lean_dec_ref(v___y_3733_);
    crate::leanh::lean_dec(v___y_3732_);
    crate::leanh::lean_dec_ref(v___y_3731_);
    return v_res_3736_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(
    mut v_declName_3737_: *mut crate::leanh::LeanObject,
    mut v_s_3738_: u8,
    mut v___y_3739_: *mut crate::leanh::LeanObject,
    mut v___y_3740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3753_: u8 = 0;
    let mut v___x_3754_: u8 = 0;
    let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3768_: u8 = 0;
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3776_: u8 = 0;
    let mut v_unused_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3779_: u8 = 0;
    let mut v_unused_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3742_ = lean_st_ref_take(v___y_3740_);
                v_env_3743_ = crate::leanh::lean_ctor_get(v___x_3742_, 0);
                v_nextMacroScope_3744_ = crate::leanh::lean_ctor_get(v___x_3742_, 1);
                v_ngen_3745_ = crate::leanh::lean_ctor_get(v___x_3742_, 2);
                v_auxDeclNGen_3746_ = crate::leanh::lean_ctor_get(v___x_3742_, 3);
                v_traceState_3747_ = crate::leanh::lean_ctor_get(v___x_3742_, 4);
                v_messages_3748_ = crate::leanh::lean_ctor_get(v___x_3742_, 6);
                v_infoState_3749_ = crate::leanh::lean_ctor_get(v___x_3742_, 7);
                v_snapshotTasks_3750_ = crate::leanh::lean_ctor_get(v___x_3742_, 8);
                v_isSharedCheck_3779_ = (!crate::leanh::lean_is_exclusive(v___x_3742_)) as u8;
                if v_isSharedCheck_3779_ == 0 {
                    v_unused_3780_ = crate::leanh::lean_ctor_get(v___x_3742_, 5);
                    crate::leanh::lean_dec(v_unused_3780_);
                    v___x_3752_ = v___x_3742_;
                    v_isShared_3753_ = v_isSharedCheck_3779_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3750_);
                    crate::leanh::lean_inc(v_infoState_3749_);
                    crate::leanh::lean_inc(v_messages_3748_);
                    crate::leanh::lean_inc(v_traceState_3747_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3746_);
                    crate::leanh::lean_inc(v_ngen_3745_);
                    crate::leanh::lean_inc(v_nextMacroScope_3744_);
                    crate::leanh::lean_inc(v_env_3743_);
                    crate::leanh::lean_dec(v___x_3742_);
                    v___x_3752_ = crate::leanh::lean_box(0);
                    v_isShared_3753_ = v_isSharedCheck_3779_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3754_ = 0;
                v___x_3755_ = crate::leanh::lean_box(0);
                v___x_3756_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(
                    v_env_3743_,
                    v_declName_3737_,
                    v_s_3738_,
                    v___x_3754_,
                    v___x_3755_,
                );
                v___x_3757_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once
                    ),
                    _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2,
                );
                if v_isShared_3753_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3752_, 5, v___x_3757_);
                    crate::leanh::lean_ctor_set(v___x_3752_, 0, v___x_3756_);
                    v___x_3759_ = v___x_3752_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3778_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 0, v___x_3756_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 1, v_nextMacroScope_3744_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 2, v_ngen_3745_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 3, v_auxDeclNGen_3746_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 4, v_traceState_3747_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 5, v___x_3757_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 6, v_messages_3748_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 7, v_infoState_3749_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 8, v_snapshotTasks_3750_);
                    v___x_3759_ = v_reuseFailAlloc_3778_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3760_ = lean_st_ref_set(v___y_3740_, v___x_3759_);
                v___x_3761_ = lean_st_ref_take(v___y_3739_);
                v_mctx_3762_ = crate::leanh::lean_ctor_get(v___x_3761_, 0);
                v_zetaDeltaFVarIds_3763_ = crate::leanh::lean_ctor_get(v___x_3761_, 2);
                v_postponed_3764_ = crate::leanh::lean_ctor_get(v___x_3761_, 3);
                v_diag_3765_ = crate::leanh::lean_ctor_get(v___x_3761_, 4);
                v_isSharedCheck_3776_ = (!crate::leanh::lean_is_exclusive(v___x_3761_)) as u8;
                if v_isSharedCheck_3776_ == 0 {
                    v_unused_3777_ = crate::leanh::lean_ctor_get(v___x_3761_, 1);
                    crate::leanh::lean_dec(v_unused_3777_);
                    v___x_3767_ = v___x_3761_;
                    v_isShared_3768_ = v_isSharedCheck_3776_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_3765_);
                    crate::leanh::lean_inc(v_postponed_3764_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_3763_);
                    crate::leanh::lean_inc(v_mctx_3762_);
                    crate::leanh::lean_dec(v___x_3761_);
                    v___x_3767_ = crate::leanh::lean_box(0);
                    v_isShared_3768_ = v_isSharedCheck_3776_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3769_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once
                    ),
                    _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3,
                );
                if v_isShared_3768_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3767_, 1, v___x_3769_);
                    v___x_3771_ = v___x_3767_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3775_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_mctx_3762_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 1, v___x_3769_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3775_,
                        2,
                        v_zetaDeltaFVarIds_3763_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 3, v_postponed_3764_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 4, v_diag_3765_);
                    v___x_3771_ = v_reuseFailAlloc_3775_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3772_ = lean_st_ref_set(v___y_3739_, v___x_3771_);
                v___x_3773_ = crate::leanh::lean_box(0);
                v___x_3774_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3774_, 0, v___x_3773_);
                return v___x_3774_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg___boxed(
    mut v_declName_3781_: *mut crate::leanh::LeanObject,
    mut v_s_3782_: *mut crate::leanh::LeanObject,
    mut v___y_3783_: *mut crate::leanh::LeanObject,
    mut v___y_3784_: *mut crate::leanh::LeanObject,
    mut v___y_3785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_boxed_3786_: u8 = 0;
    let mut v_res_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_s_boxed_3786_ = (crate::leanh::lean_unbox(v_s_3782_) as u8);
    v_res_3787_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(v_declName_3781_, v_s_boxed_3786_, v___y_3783_, v___y_3784_);
    crate::leanh::lean_dec(v___y_3784_);
    crate::leanh::lean_dec(v___y_3783_);
    return v_res_3787_;
}
pub unsafe fn l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10(
    mut v_declName_3788_: *mut crate::leanh::LeanObject,
    mut v___y_3789_: *mut crate::leanh::LeanObject,
    mut v___y_3790_: *mut crate::leanh::LeanObject,
    mut v___y_3791_: *mut crate::leanh::LeanObject,
    mut v___y_3792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3794_: u8 = 0;
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3794_ = 0;
    v___x_3795_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(v_declName_3788_, v___x_3794_, v___y_3790_, v___y_3792_);
    return v___x_3795_;
}
pub unsafe fn l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10___boxed(
    mut v_declName_3796_: *mut crate::leanh::LeanObject,
    mut v___y_3797_: *mut crate::leanh::LeanObject,
    mut v___y_3798_: *mut crate::leanh::LeanObject,
    mut v___y_3799_: *mut crate::leanh::LeanObject,
    mut v___y_3800_: *mut crate::leanh::LeanObject,
    mut v___y_3801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3802_ = l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10(
        v_declName_3796_,
        v___y_3797_,
        v___y_3798_,
        v___y_3799_,
        v___y_3800_,
    );
    crate::leanh::lean_dec(v___y_3800_);
    crate::leanh::lean_dec_ref(v___y_3799_);
    crate::leanh::lean_dec(v___y_3798_);
    crate::leanh::lean_dec_ref(v___y_3797_);
    return v_res_3802_;
}
pub unsafe fn l_mkCtorIdx___lam__1(
    mut v___x_3809_: *mut crate::leanh::LeanObject,
    mut v___x_3810_: *mut crate::leanh::LeanObject,
    mut v_xs_3811_: *mut crate::leanh::LeanObject,
    mut v___x_3812_: u8,
    mut v___x_3813_: u8,
    mut v_val_3814_: *mut crate::leanh::LeanObject,
    mut v___x_3815_: *mut crate::leanh::LeanObject,
    mut v___x_3816_: *mut crate::leanh::LeanObject,
    mut v___x_3817_: *mut crate::leanh::LeanObject,
    mut v___x_3818_: *mut crate::leanh::LeanObject,
    mut v_ctors_3819_: *mut crate::leanh::LeanObject,
    mut v___x_3820_: *mut crate::leanh::LeanObject,
    mut v___x_3821_: *mut crate::leanh::LeanObject,
    mut v_levelParams_3822_: *mut crate::leanh::LeanObject,
    mut v_indName_3823_: *mut crate::leanh::LeanObject,
    mut v___y_3824_: *mut crate::leanh::LeanObject,
    mut v___y_3825_: *mut crate::leanh::LeanObject,
    mut v___y_3826_: *mut crate::leanh::LeanObject,
    mut v___y_3827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3850_: u8 = 0;
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3863_: u8 = 0;
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3879_: u8 = 0;
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3891_: u8 = 0;
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3898_: u8 = 0;
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3906_: u8 = 0;
    let mut v_unused_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3909_: u8 = 0;
    let mut v_unused_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3912_: u8 = 0;
    let mut v_unused_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3915_: u8 = 0;
    let mut v_unused_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3918_: u8 = 0;
    let mut v_unused_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: u8 = 0;
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: u32 = 0;
    let mut v___x_3935_: u32 = 0;
    let mut v___x_3936_: u32 = 0;
    let mut v___x_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3942_: u8 = 0;
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3956_: u8 = 0;
    let mut v___x_3957_: u8 = 0;
    let mut v___x_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3969_: u8 = 0;
    let mut v___x_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: u8 = 0;
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3987_: u8 = 0;
    let mut v___x_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4000_: u8 = 0;
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4006_: u8 = 0;
    let mut v_unused_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4009_: u8 = 0;
    let mut v_unused_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4012_: u8 = 0;
    let mut v_isSharedCheck_4013_: u8 = 0;
    let mut v_a_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4017_: u8 = 0;
    let mut v___x_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4021_: u8 = 0;
    let mut v___y_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: u8 = 0;
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4041_: u8 = 0;
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4054_: u8 = 0;
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4060_: u8 = 0;
    let mut v_unused_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4063_: u8 = 0;
    let mut v_unused_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4077_: u8 = 0;
    let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4090_: u8 = 0;
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4106_: u8 = 0;
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4118_: u8 = 0;
    let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: u8 = 0;
    let mut v___x_4125_: u8 = 0;
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4128_: u8 = 0;
    let mut v_unused_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4131_: u8 = 0;
    let mut v_unused_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4134_: u8 = 0;
    let mut v_unused_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4137_: u8 = 0;
    let mut v_unused_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4140_: u8 = 0;
    let mut v_a_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4144_: u8 = 0;
    let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4148_: u8 = 0;
    let mut v_a_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4152_: u8 = 0;
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4156_: u8 = 0;
    let mut v_a_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4160_: u8 = 0;
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4164_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v___x_3810_);
                crate::leanh::lean_inc_ref(v___x_3809_);
                v___x_3920_ = l_Lean_mkArrow(v___x_3809_, v___x_3810_, v___y_3826_, v___y_3827_);
                if crate::leanh::lean_obj_tag(v___x_3920_) == 0 {
                    v_a_3921_ = crate::leanh::lean_ctor_get(v___x_3920_, 0);
                    crate::leanh::lean_inc(v_a_3921_);
                    crate::leanh::lean_dec_ref_known(v___x_3920_, 1);
                    v___x_3922_ = 1;
                    v___x_3923_ = l_Lean_Meta_mkForallFVars(
                        v_xs_3811_,
                        v_a_3921_,
                        v___x_3812_,
                        v___x_3813_,
                        v___x_3813_,
                        v___x_3922_,
                        v___y_3824_,
                        v___y_3825_,
                        v___y_3826_,
                        v___y_3827_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3923_) == 0 {
                        v_a_3924_ = crate::leanh::lean_ctor_get(v___x_3923_, 0);
                        crate::leanh::lean_inc(v_a_3924_);
                        crate::leanh::lean_dec_ref_known(v___x_3923_, 1);
                        v___x_3925_ = crate::leanh::lean_box((v___x_3812_) as usize);
                        v___x_3926_ = crate::leanh::lean_box((v___x_3813_) as usize);
                        v___x_3927_ = crate::leanh::lean_box((v___x_3922_) as usize);
                        crate::leanh::lean_inc(v___x_3816_);
                        crate::leanh::lean_inc_ref(v_val_3814_);
                        v___f_3928_ = crate::leanh::lean_alloc_closure(
                            l_mkCtorIdx___lam__0___boxed as *mut core::ffi::c_void,
                            18,
                            12,
                        );
                        crate::leanh::lean_closure_set(v___f_3928_, 0, v_xs_3811_);
                        crate::leanh::lean_closure_set(v___f_3928_, 1, v___x_3925_);
                        crate::leanh::lean_closure_set(v___f_3928_, 2, v___x_3926_);
                        crate::leanh::lean_closure_set(v___f_3928_, 3, v___x_3927_);
                        crate::leanh::lean_closure_set(v___f_3928_, 4, v_val_3814_);
                        crate::leanh::lean_closure_set(v___f_3928_, 5, v___x_3815_);
                        crate::leanh::lean_closure_set(v___f_3928_, 6, v___x_3810_);
                        crate::leanh::lean_closure_set(v___f_3928_, 7, v___x_3816_);
                        crate::leanh::lean_closure_set(v___f_3928_, 8, v___x_3817_);
                        crate::leanh::lean_closure_set(v___f_3928_, 9, v___x_3818_);
                        crate::leanh::lean_closure_set(v___f_3928_, 10, v_ctors_3819_);
                        crate::leanh::lean_closure_set(v___f_3928_, 11, v___x_3820_);
                        v___x_3929_ = l_mkCtorIdx___lam__1___closed__3;
                        v___x_3930_ =
                            l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg(
                                v___x_3929_,
                                v___x_3809_,
                                v___f_3928_,
                                v___y_3824_,
                                v___y_3825_,
                                v___y_3826_,
                                v___y_3827_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_3930_) == 0 {
                            v_a_3931_ = crate::leanh::lean_ctor_get(v___x_3930_, 0);
                            crate::leanh::lean_inc_n(v_a_3931_, 2);
                            crate::leanh::lean_dec_ref_known(v___x_3930_, 1);
                            v___x_3932_ = lean_st_ref_get(v___y_3827_);
                            v_env_3933_ = crate::leanh::lean_ctor_get(v___x_3932_, 0);
                            crate::leanh::lean_inc_ref(v_env_3933_);
                            crate::leanh::lean_dec(v___x_3932_);
                            v___x_3934_ = l_Lean_getMaxHeight(v_env_3933_, v_a_3931_);
                            v___x_3935_ = 1;
                            v___x_3936_ = lean_uint32_add(v___x_3934_, v___x_3935_);
                            v___x_3937_ = crate::leanh::lean_alloc_ctor(2, 0, (4) as u32);
                            crate::leanh::lean_ctor_set_uint32(v___x_3937_, 0 as u32, v___x_3936_);
                            crate::leanh::lean_inc(v_a_3924_);
                            crate::leanh::lean_inc(v_levelParams_3822_);
                            crate::leanh::lean_inc(v___x_3821_);
                            v___x_3938_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(v___x_3821_, v_levelParams_3822_, v_a_3924_, v_a_3931_, v___x_3937_, v___y_3827_);
                            v_a_3939_ = crate::leanh::lean_ctor_get(v___x_3938_, 0);
                            v_isSharedCheck_4140_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3938_)) as u8;
                            if v_isSharedCheck_4140_ == 0 {
                                v___x_3941_ = v___x_3938_;
                                v_isShared_3942_ = v_isSharedCheck_4140_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3939_);
                                crate::leanh::lean_dec(v___x_3938_);
                                v___x_3941_ = crate::leanh::lean_box(0);
                                v_isShared_3942_ = v_isSharedCheck_4140_;
                                state = 12;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3924_);
                            crate::leanh::lean_dec(v_indName_3823_);
                            crate::leanh::lean_dec(v_levelParams_3822_);
                            crate::leanh::lean_dec(v___x_3821_);
                            crate::leanh::lean_dec(v___x_3816_);
                            crate::leanh::lean_dec_ref(v_val_3814_);
                            v_a_4141_ = crate::leanh::lean_ctor_get(v___x_3930_, 0);
                            v_isSharedCheck_4148_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3930_)) as u8;
                            if v_isSharedCheck_4148_ == 0 {
                                v___x_4143_ = v___x_3930_;
                                v_isShared_4144_ = v_isSharedCheck_4148_;
                                state = 38;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4141_);
                                crate::leanh::lean_dec(v___x_3930_);
                                v___x_4143_ = crate::leanh::lean_box(0);
                                v_isShared_4144_ = v_isSharedCheck_4148_;
                                state = 38;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_indName_3823_);
                        crate::leanh::lean_dec(v_levelParams_3822_);
                        crate::leanh::lean_dec(v___x_3821_);
                        crate::leanh::lean_dec(v___x_3820_);
                        crate::leanh::lean_dec(v_ctors_3819_);
                        crate::leanh::lean_dec_ref(v___x_3818_);
                        crate::leanh::lean_dec(v___x_3817_);
                        crate::leanh::lean_dec(v___x_3816_);
                        crate::leanh::lean_dec_ref(v___x_3815_);
                        crate::leanh::lean_dec_ref(v_val_3814_);
                        crate::leanh::lean_dec_ref(v_xs_3811_);
                        crate::leanh::lean_dec_ref(v___x_3810_);
                        crate::leanh::lean_dec_ref(v___x_3809_);
                        v_a_4149_ = crate::leanh::lean_ctor_get(v___x_3923_, 0);
                        v_isSharedCheck_4156_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3923_)) as u8;
                        if v_isSharedCheck_4156_ == 0 {
                            v___x_4151_ = v___x_3923_;
                            v_isShared_4152_ = v_isSharedCheck_4156_;
                            state = 40;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4149_);
                            crate::leanh::lean_dec(v___x_3923_);
                            v___x_4151_ = crate::leanh::lean_box(0);
                            v_isShared_4152_ = v_isSharedCheck_4156_;
                            state = 40;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_indName_3823_);
                    crate::leanh::lean_dec(v_levelParams_3822_);
                    crate::leanh::lean_dec(v___x_3821_);
                    crate::leanh::lean_dec(v___x_3820_);
                    crate::leanh::lean_dec(v_ctors_3819_);
                    crate::leanh::lean_dec_ref(v___x_3818_);
                    crate::leanh::lean_dec(v___x_3817_);
                    crate::leanh::lean_dec(v___x_3816_);
                    crate::leanh::lean_dec_ref(v___x_3815_);
                    crate::leanh::lean_dec_ref(v_val_3814_);
                    crate::leanh::lean_dec_ref(v_xs_3811_);
                    crate::leanh::lean_dec_ref(v___x_3810_);
                    crate::leanh::lean_dec_ref(v___x_3809_);
                    v_a_4157_ = crate::leanh::lean_ctor_get(v___x_3920_, 0);
                    v_isSharedCheck_4164_ = (!crate::leanh::lean_is_exclusive(v___x_3920_)) as u8;
                    if v_isSharedCheck_4164_ == 0 {
                        v___x_4159_ = v___x_3920_;
                        v_isShared_4160_ = v_isSharedCheck_4164_;
                        state = 42;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4157_);
                        crate::leanh::lean_dec(v___x_3920_);
                        v___x_4159_ = crate::leanh::lean_box(0);
                        v_isShared_4160_ = v_isSharedCheck_4164_;
                        state = 42;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3835_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3836_ = lean_mk_empty_array_with_capacity(v___x_3835_);
                crate::leanh::lean_inc(v___y_3830_);
                v___x_3837_ = lean_array_push(v___x_3836_, v___y_3830_);
                v___x_3838_ =
                    l_Lean_compileDecls(v___x_3837_, v___x_3813_, v___y_3833_, v___y_3834_);
                if crate::leanh::lean_obj_tag(v___x_3838_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3838_, 1);
                    v___x_3839_ = lean_st_ref_take(v___y_3834_);
                    v_env_3840_ = crate::leanh::lean_ctor_get(v___x_3839_, 0);
                    v_nextMacroScope_3841_ = crate::leanh::lean_ctor_get(v___x_3839_, 1);
                    v_ngen_3842_ = crate::leanh::lean_ctor_get(v___x_3839_, 2);
                    v_auxDeclNGen_3843_ = crate::leanh::lean_ctor_get(v___x_3839_, 3);
                    v_traceState_3844_ = crate::leanh::lean_ctor_get(v___x_3839_, 4);
                    v_messages_3845_ = crate::leanh::lean_ctor_get(v___x_3839_, 6);
                    v_infoState_3846_ = crate::leanh::lean_ctor_get(v___x_3839_, 7);
                    v_snapshotTasks_3847_ = crate::leanh::lean_ctor_get(v___x_3839_, 8);
                    v_isSharedCheck_3918_ = (!crate::leanh::lean_is_exclusive(v___x_3839_)) as u8;
                    if v_isSharedCheck_3918_ == 0 {
                        v_unused_3919_ = crate::leanh::lean_ctor_get(v___x_3839_, 5);
                        crate::leanh::lean_dec(v_unused_3919_);
                        v___x_3849_ = v___x_3839_;
                        v_isShared_3850_ = v_isSharedCheck_3918_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snapshotTasks_3847_);
                        crate::leanh::lean_inc(v_infoState_3846_);
                        crate::leanh::lean_inc(v_messages_3845_);
                        crate::leanh::lean_inc(v_traceState_3844_);
                        crate::leanh::lean_inc(v_auxDeclNGen_3843_);
                        crate::leanh::lean_inc(v_ngen_3842_);
                        crate::leanh::lean_inc(v_nextMacroScope_3841_);
                        crate::leanh::lean_inc(v_env_3840_);
                        crate::leanh::lean_dec(v___x_3839_);
                        v___x_3849_ = crate::leanh::lean_box(0);
                        v_isShared_3850_ = v_isSharedCheck_3918_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_3830_);
                    crate::leanh::lean_dec(v___x_3821_);
                    return v___x_3838_;
                }
            }
            2 => {
                crate::leanh::lean_inc(v___y_3830_);
                v___x_3851_ = l_Lean_Meta_addToCompletionBlackList(v_env_3840_, v___y_3830_);
                v___x_3852_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once
                    ),
                    _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2,
                );
                if v_isShared_3850_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3849_, 5, v___x_3852_);
                    crate::leanh::lean_ctor_set(v___x_3849_, 0, v___x_3851_);
                    v___x_3854_ = v___x_3849_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3917_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3917_, 0, v___x_3851_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3917_, 1, v_nextMacroScope_3841_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3917_, 2, v_ngen_3842_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3917_, 3, v_auxDeclNGen_3843_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3917_, 4, v_traceState_3844_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3917_, 5, v___x_3852_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3917_, 6, v_messages_3845_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3917_, 7, v_infoState_3846_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3917_, 8, v_snapshotTasks_3847_);
                    v___x_3854_ = v_reuseFailAlloc_3917_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3855_ = lean_st_ref_set(v___y_3834_, v___x_3854_);
                v___x_3856_ = lean_st_ref_take(v___y_3832_);
                v_mctx_3857_ = crate::leanh::lean_ctor_get(v___x_3856_, 0);
                v_zetaDeltaFVarIds_3858_ = crate::leanh::lean_ctor_get(v___x_3856_, 2);
                v_postponed_3859_ = crate::leanh::lean_ctor_get(v___x_3856_, 3);
                v_diag_3860_ = crate::leanh::lean_ctor_get(v___x_3856_, 4);
                v_isSharedCheck_3915_ = (!crate::leanh::lean_is_exclusive(v___x_3856_)) as u8;
                if v_isSharedCheck_3915_ == 0 {
                    v_unused_3916_ = crate::leanh::lean_ctor_get(v___x_3856_, 1);
                    crate::leanh::lean_dec(v_unused_3916_);
                    v___x_3862_ = v___x_3856_;
                    v_isShared_3863_ = v_isSharedCheck_3915_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_3860_);
                    crate::leanh::lean_inc(v_postponed_3859_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_3858_);
                    crate::leanh::lean_inc(v_mctx_3857_);
                    crate::leanh::lean_dec(v___x_3856_);
                    v___x_3862_ = crate::leanh::lean_box(0);
                    v_isShared_3863_ = v_isSharedCheck_3915_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3864_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once
                    ),
                    _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3,
                );
                if v_isShared_3863_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3862_, 1, v___x_3864_);
                    v___x_3866_ = v___x_3862_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3914_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_mctx_3857_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3914_, 1, v___x_3864_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3914_,
                        2,
                        v_zetaDeltaFVarIds_3858_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3914_, 3, v_postponed_3859_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3914_, 4, v_diag_3860_);
                    v___x_3866_ = v_reuseFailAlloc_3914_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3867_ = lean_st_ref_set(v___y_3832_, v___x_3866_);
                v___x_3868_ = lean_st_ref_take(v___y_3834_);
                v_env_3869_ = crate::leanh::lean_ctor_get(v___x_3868_, 0);
                v_nextMacroScope_3870_ = crate::leanh::lean_ctor_get(v___x_3868_, 1);
                v_ngen_3871_ = crate::leanh::lean_ctor_get(v___x_3868_, 2);
                v_auxDeclNGen_3872_ = crate::leanh::lean_ctor_get(v___x_3868_, 3);
                v_traceState_3873_ = crate::leanh::lean_ctor_get(v___x_3868_, 4);
                v_messages_3874_ = crate::leanh::lean_ctor_get(v___x_3868_, 6);
                v_infoState_3875_ = crate::leanh::lean_ctor_get(v___x_3868_, 7);
                v_snapshotTasks_3876_ = crate::leanh::lean_ctor_get(v___x_3868_, 8);
                v_isSharedCheck_3912_ = (!crate::leanh::lean_is_exclusive(v___x_3868_)) as u8;
                if v_isSharedCheck_3912_ == 0 {
                    v_unused_3913_ = crate::leanh::lean_ctor_get(v___x_3868_, 5);
                    crate::leanh::lean_dec(v_unused_3913_);
                    v___x_3878_ = v___x_3868_;
                    v_isShared_3879_ = v_isSharedCheck_3912_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3876_);
                    crate::leanh::lean_inc(v_infoState_3875_);
                    crate::leanh::lean_inc(v_messages_3874_);
                    crate::leanh::lean_inc(v_traceState_3873_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3872_);
                    crate::leanh::lean_inc(v_ngen_3871_);
                    crate::leanh::lean_inc(v_nextMacroScope_3870_);
                    crate::leanh::lean_inc(v_env_3869_);
                    crate::leanh::lean_dec(v___x_3868_);
                    v___x_3878_ = crate::leanh::lean_box(0);
                    v_isShared_3879_ = v_isSharedCheck_3912_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                crate::leanh::lean_inc(v___y_3830_);
                v___x_3880_ = l_Lean_addProtected(v_env_3869_, v___y_3830_);
                if v_isShared_3879_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3878_, 5, v___x_3852_);
                    crate::leanh::lean_ctor_set(v___x_3878_, 0, v___x_3880_);
                    v___x_3882_ = v___x_3878_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3911_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 0, v___x_3880_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 1, v_nextMacroScope_3870_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 2, v_ngen_3871_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 3, v_auxDeclNGen_3872_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 4, v_traceState_3873_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 5, v___x_3852_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 6, v_messages_3874_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 7, v_infoState_3875_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 8, v_snapshotTasks_3876_);
                    v___x_3882_ = v_reuseFailAlloc_3911_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3883_ = lean_st_ref_set(v___y_3834_, v___x_3882_);
                v___x_3884_ = lean_st_ref_take(v___y_3832_);
                v_mctx_3885_ = crate::leanh::lean_ctor_get(v___x_3884_, 0);
                v_zetaDeltaFVarIds_3886_ = crate::leanh::lean_ctor_get(v___x_3884_, 2);
                v_postponed_3887_ = crate::leanh::lean_ctor_get(v___x_3884_, 3);
                v_diag_3888_ = crate::leanh::lean_ctor_get(v___x_3884_, 4);
                v_isSharedCheck_3909_ = (!crate::leanh::lean_is_exclusive(v___x_3884_)) as u8;
                if v_isSharedCheck_3909_ == 0 {
                    v_unused_3910_ = crate::leanh::lean_ctor_get(v___x_3884_, 1);
                    crate::leanh::lean_dec(v_unused_3910_);
                    v___x_3890_ = v___x_3884_;
                    v_isShared_3891_ = v_isSharedCheck_3909_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_3888_);
                    crate::leanh::lean_inc(v_postponed_3887_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_3886_);
                    crate::leanh::lean_inc(v_mctx_3885_);
                    crate::leanh::lean_dec(v___x_3884_);
                    v___x_3890_ = crate::leanh::lean_box(0);
                    v_isShared_3891_ = v_isSharedCheck_3909_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_3891_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3890_, 1, v___x_3864_);
                    v___x_3893_ = v___x_3890_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3908_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_mctx_3885_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3908_, 1, v___x_3864_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3908_,
                        2,
                        v_zetaDeltaFVarIds_3886_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3908_, 3, v_postponed_3887_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3908_, 4, v_diag_3888_);
                    v___x_3893_ = v_reuseFailAlloc_3908_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3894_ = lean_st_ref_set(v___y_3832_, v___x_3893_);
                crate::leanh::lean_inc(v___y_3830_);
                v___x_3895_ = l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10(
                    v___y_3830_,
                    v___y_3831_,
                    v___y_3832_,
                    v___y_3833_,
                    v___y_3834_,
                );
                v_isSharedCheck_3906_ = (!crate::leanh::lean_is_exclusive(v___x_3895_)) as u8;
                if v_isSharedCheck_3906_ == 0 {
                    v_unused_3907_ = crate::leanh::lean_ctor_get(v___x_3895_, 0);
                    crate::leanh::lean_dec(v_unused_3907_);
                    v___x_3897_ = v___x_3895_;
                    v_isShared_3898_ = v_isSharedCheck_3906_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_3895_);
                    v___x_3897_ = crate::leanh::lean_box(0);
                    v_isShared_3898_ = v_isSharedCheck_3906_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_3898_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3897_, 1);
                    crate::leanh::lean_ctor_set(v___x_3897_, 0, v___x_3821_);
                    v___x_3900_ = v___x_3897_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3905_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3905_, 0, v___x_3821_);
                    v___x_3900_ = v_reuseFailAlloc_3905_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_3901_ = crate::leanh::lean_box(0);
                v___x_3902_ = l_mkCtorIdx___lam__1___closed__1;
                v___x_3903_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3903_, 0, v___x_3900_);
                crate::leanh::lean_ctor_set(v___x_3903_, 1, v___x_3901_);
                crate::leanh::lean_ctor_set(v___x_3903_, 2, v___x_3902_);
                v___x_3904_ = l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11(
                    v___y_3830_,
                    v___x_3903_,
                    v___y_3831_,
                    v___y_3832_,
                    v___y_3833_,
                    v___y_3834_,
                );
                return v___x_3904_;
            }
            12 => {
                if v_isShared_3942_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3941_, 1);
                    v___x_3944_ = v___x_3941_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4139_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4139_, 0, v_a_3939_);
                    v___x_3944_ = v_reuseFailAlloc_4139_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                crate::leanh::lean_inc_ref(v___x_3944_);
                v___x_4065_ = l_Lean_addDecl(v___x_3944_, v___x_3812_, v___y_3826_, v___y_3827_);
                if crate::leanh::lean_obj_tag(v___x_4065_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4065_, 1);
                    v___x_4066_ = lean_st_ref_take(v___y_3827_);
                    v_env_4067_ = crate::leanh::lean_ctor_get(v___x_4066_, 0);
                    v_nextMacroScope_4068_ = crate::leanh::lean_ctor_get(v___x_4066_, 1);
                    v_ngen_4069_ = crate::leanh::lean_ctor_get(v___x_4066_, 2);
                    v_auxDeclNGen_4070_ = crate::leanh::lean_ctor_get(v___x_4066_, 3);
                    v_traceState_4071_ = crate::leanh::lean_ctor_get(v___x_4066_, 4);
                    v_messages_4072_ = crate::leanh::lean_ctor_get(v___x_4066_, 6);
                    v_infoState_4073_ = crate::leanh::lean_ctor_get(v___x_4066_, 7);
                    v_snapshotTasks_4074_ = crate::leanh::lean_ctor_get(v___x_4066_, 8);
                    v_isSharedCheck_4137_ = (!crate::leanh::lean_is_exclusive(v___x_4066_)) as u8;
                    if v_isSharedCheck_4137_ == 0 {
                        v_unused_4138_ = crate::leanh::lean_ctor_get(v___x_4066_, 5);
                        crate::leanh::lean_dec(v_unused_4138_);
                        v___x_4076_ = v___x_4066_;
                        v_isShared_4077_ = v_isSharedCheck_4137_;
                        state = 30;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snapshotTasks_4074_);
                        crate::leanh::lean_inc(v_infoState_4073_);
                        crate::leanh::lean_inc(v_messages_4072_);
                        crate::leanh::lean_inc(v_traceState_4071_);
                        crate::leanh::lean_inc(v_auxDeclNGen_4070_);
                        crate::leanh::lean_inc(v_ngen_4069_);
                        crate::leanh::lean_inc(v_nextMacroScope_4068_);
                        crate::leanh::lean_inc(v_env_4067_);
                        crate::leanh::lean_dec(v___x_4066_);
                        v___x_4076_ = crate::leanh::lean_box(0);
                        v_isShared_4077_ = v_isSharedCheck_4137_;
                        state = 30;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3944_);
                    crate::leanh::lean_dec(v_a_3924_);
                    crate::leanh::lean_dec(v_indName_3823_);
                    crate::leanh::lean_dec(v_levelParams_3822_);
                    crate::leanh::lean_dec(v___x_3821_);
                    crate::leanh::lean_dec(v___x_3816_);
                    crate::leanh::lean_dec_ref(v_val_3814_);
                    return v___x_4065_;
                }
            }
            14 => {
                v___x_3950_ =
                    l_Lean_compileDecl(v___x_3944_, v___x_3813_, v___y_3948_, v___y_3949_);
                if crate::leanh::lean_obj_tag(v___x_3950_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3950_, 1);
                    crate::leanh::lean_inc(v___x_3821_);
                    v___x_3951_ =
                        l_Lean_enableRealizationsForConst(v___x_3821_, v___y_3948_, v___y_3949_);
                    if crate::leanh::lean_obj_tag(v___x_3951_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3951_, 1);
                        crate::leanh::lean_inc(v_indName_3823_);
                        v___x_3952_ = l_Lean_isEnumType___at___00mkCtorIdx_spec__9(
                            v_indName_3823_,
                            v___y_3946_,
                            v___y_3947_,
                            v___y_3948_,
                            v___y_3949_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3952_) == 0 {
                            v_a_3953_ = crate::leanh::lean_ctor_get(v___x_3952_, 0);
                            v_isSharedCheck_4013_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3952_)) as u8;
                            if v_isSharedCheck_4013_ == 0 {
                                v___x_3955_ = v___x_3952_;
                                v_isShared_3956_ = v_isSharedCheck_4013_;
                                state = 15;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3953_);
                                crate::leanh::lean_dec(v___x_3952_);
                                v___x_3955_ = crate::leanh::lean_box(0);
                                v_isShared_3956_ = v_isSharedCheck_4013_;
                                state = 15;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3924_);
                            crate::leanh::lean_dec(v_indName_3823_);
                            crate::leanh::lean_dec(v_levelParams_3822_);
                            crate::leanh::lean_dec(v___x_3821_);
                            crate::leanh::lean_dec(v___x_3816_);
                            v_a_4014_ = crate::leanh::lean_ctor_get(v___x_3952_, 0);
                            v_isSharedCheck_4021_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3952_)) as u8;
                            if v_isSharedCheck_4021_ == 0 {
                                v___x_4016_ = v___x_3952_;
                                v_isShared_4017_ = v_isSharedCheck_4021_;
                                state = 23;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4014_);
                                crate::leanh::lean_dec(v___x_3952_);
                                v___x_4016_ = crate::leanh::lean_box(0);
                                v_isShared_4017_ = v_isSharedCheck_4021_;
                                state = 23;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3924_);
                        crate::leanh::lean_dec(v_indName_3823_);
                        crate::leanh::lean_dec(v_levelParams_3822_);
                        crate::leanh::lean_dec(v___x_3821_);
                        crate::leanh::lean_dec(v___x_3816_);
                        return v___x_3951_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3924_);
                    crate::leanh::lean_dec(v_indName_3823_);
                    crate::leanh::lean_dec(v_levelParams_3822_);
                    crate::leanh::lean_dec(v___x_3821_);
                    crate::leanh::lean_dec(v___x_3816_);
                    return v___x_3950_;
                }
            }
            15 => {
                v___x_3957_ = (crate::leanh::lean_unbox(v_a_3953_) as u8);
                crate::leanh::lean_dec(v_a_3953_);
                if v___x_3957_ == 0 {
                    crate::leanh::lean_dec(v_a_3924_);
                    crate::leanh::lean_dec(v_indName_3823_);
                    crate::leanh::lean_dec(v_levelParams_3822_);
                    crate::leanh::lean_dec(v___x_3821_);
                    crate::leanh::lean_dec(v___x_3816_);
                    v___x_3958_ = crate::leanh::lean_box(0);
                    if v_isShared_3956_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3955_, 0, v___x_3958_);
                        v___x_3960_ = v___x_3955_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_3961_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3961_, 0, v___x_3958_);
                        v___x_3960_ = v_reuseFailAlloc_3961_;
                        state = 16;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3955_);
                    crate::leanh::lean_inc(v_indName_3823_);
                    v___x_3962_ = l_mkToCtorIdxName(v_indName_3823_);
                    crate::leanh::lean_inc(v___x_3821_);
                    v___x_3963_ = l_Lean_mkConst(v___x_3821_, v___x_3816_);
                    v___x_3964_ = crate::leanh::lean_box(1);
                    crate::leanh::lean_inc(v___x_3962_);
                    v___x_3965_ =
                        l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(
                            v___x_3962_,
                            v_levelParams_3822_,
                            v_a_3924_,
                            v___x_3963_,
                            v___x_3964_,
                            v___y_3949_,
                        );
                    v_a_3966_ = crate::leanh::lean_ctor_get(v___x_3965_, 0);
                    v_isSharedCheck_4012_ = (!crate::leanh::lean_is_exclusive(v___x_3965_)) as u8;
                    if v_isSharedCheck_4012_ == 0 {
                        v___x_3968_ = v___x_3965_;
                        v_isShared_3969_ = v_isSharedCheck_4012_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3966_);
                        crate::leanh::lean_dec(v___x_3965_);
                        v___x_3968_ = crate::leanh::lean_box(0);
                        v_isShared_3969_ = v_isSharedCheck_4012_;
                        state = 17;
                        continue;
                    }
                }
            }
            16 => {
                return v___x_3960_;
            }
            17 => {
                if v_isShared_3969_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3968_, 1);
                    v___x_3971_ = v___x_3968_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4011_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_a_3966_);
                    v___x_3971_ = v_reuseFailAlloc_4011_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_3972_ = l_Lean_addDecl(v___x_3971_, v___x_3812_, v___y_3948_, v___y_3949_);
                if crate::leanh::lean_obj_tag(v___x_3972_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3972_, 1);
                    v___x_3973_ = lean_st_ref_get(v___y_3949_);
                    v_env_3974_ = crate::leanh::lean_ctor_get(v___x_3973_, 0);
                    crate::leanh::lean_inc_ref(v_env_3974_);
                    crate::leanh::lean_dec(v___x_3973_);
                    v___x_3975_ = l_Lean_isMarkedMeta(v_env_3974_, v_indName_3823_);
                    if v___x_3975_ == 0 {
                        v___y_3830_ = v___x_3962_;
                        v___y_3831_ = v___y_3946_;
                        v___y_3832_ = v___y_3947_;
                        v___y_3833_ = v___y_3948_;
                        v___y_3834_ = v___y_3949_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3976_ = lean_st_ref_take(v___y_3949_);
                        v_env_3977_ = crate::leanh::lean_ctor_get(v___x_3976_, 0);
                        v_nextMacroScope_3978_ = crate::leanh::lean_ctor_get(v___x_3976_, 1);
                        v_ngen_3979_ = crate::leanh::lean_ctor_get(v___x_3976_, 2);
                        v_auxDeclNGen_3980_ = crate::leanh::lean_ctor_get(v___x_3976_, 3);
                        v_traceState_3981_ = crate::leanh::lean_ctor_get(v___x_3976_, 4);
                        v_messages_3982_ = crate::leanh::lean_ctor_get(v___x_3976_, 6);
                        v_infoState_3983_ = crate::leanh::lean_ctor_get(v___x_3976_, 7);
                        v_snapshotTasks_3984_ = crate::leanh::lean_ctor_get(v___x_3976_, 8);
                        v_isSharedCheck_4009_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3976_)) as u8;
                        if v_isSharedCheck_4009_ == 0 {
                            v_unused_4010_ = crate::leanh::lean_ctor_get(v___x_3976_, 5);
                            crate::leanh::lean_dec(v_unused_4010_);
                            v___x_3986_ = v___x_3976_;
                            v_isShared_3987_ = v_isSharedCheck_4009_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snapshotTasks_3984_);
                            crate::leanh::lean_inc(v_infoState_3983_);
                            crate::leanh::lean_inc(v_messages_3982_);
                            crate::leanh::lean_inc(v_traceState_3981_);
                            crate::leanh::lean_inc(v_auxDeclNGen_3980_);
                            crate::leanh::lean_inc(v_ngen_3979_);
                            crate::leanh::lean_inc(v_nextMacroScope_3978_);
                            crate::leanh::lean_inc(v_env_3977_);
                            crate::leanh::lean_dec(v___x_3976_);
                            v___x_3986_ = crate::leanh::lean_box(0);
                            v_isShared_3987_ = v_isSharedCheck_4009_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3962_);
                    crate::leanh::lean_dec(v_indName_3823_);
                    crate::leanh::lean_dec(v___x_3821_);
                    return v___x_3972_;
                }
            }
            19 => {
                crate::leanh::lean_inc(v___x_3962_);
                v___x_3988_ = l_Lean_markMeta(v_env_3977_, v___x_3962_);
                v___x_3989_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once
                    ),
                    _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2,
                );
                if v_isShared_3987_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3986_, 5, v___x_3989_);
                    crate::leanh::lean_ctor_set(v___x_3986_, 0, v___x_3988_);
                    v___x_3991_ = v___x_3986_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4008_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4008_, 0, v___x_3988_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4008_, 1, v_nextMacroScope_3978_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4008_, 2, v_ngen_3979_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4008_, 3, v_auxDeclNGen_3980_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4008_, 4, v_traceState_3981_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4008_, 5, v___x_3989_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4008_, 6, v_messages_3982_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4008_, 7, v_infoState_3983_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4008_, 8, v_snapshotTasks_3984_);
                    v___x_3991_ = v_reuseFailAlloc_4008_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_3992_ = lean_st_ref_set(v___y_3949_, v___x_3991_);
                v___x_3993_ = lean_st_ref_take(v___y_3947_);
                v_mctx_3994_ = crate::leanh::lean_ctor_get(v___x_3993_, 0);
                v_zetaDeltaFVarIds_3995_ = crate::leanh::lean_ctor_get(v___x_3993_, 2);
                v_postponed_3996_ = crate::leanh::lean_ctor_get(v___x_3993_, 3);
                v_diag_3997_ = crate::leanh::lean_ctor_get(v___x_3993_, 4);
                v_isSharedCheck_4006_ = (!crate::leanh::lean_is_exclusive(v___x_3993_)) as u8;
                if v_isSharedCheck_4006_ == 0 {
                    v_unused_4007_ = crate::leanh::lean_ctor_get(v___x_3993_, 1);
                    crate::leanh::lean_dec(v_unused_4007_);
                    v___x_3999_ = v___x_3993_;
                    v_isShared_4000_ = v_isSharedCheck_4006_;
                    state = 21;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_3997_);
                    crate::leanh::lean_inc(v_postponed_3996_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_3995_);
                    crate::leanh::lean_inc(v_mctx_3994_);
                    crate::leanh::lean_dec(v___x_3993_);
                    v___x_3999_ = crate::leanh::lean_box(0);
                    v_isShared_4000_ = v_isSharedCheck_4006_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_4001_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once
                    ),
                    _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3,
                );
                if v_isShared_4000_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3999_, 1, v___x_4001_);
                    v___x_4003_ = v___x_3999_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4005_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_mctx_3994_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4005_, 1, v___x_4001_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4005_,
                        2,
                        v_zetaDeltaFVarIds_3995_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4005_, 3, v_postponed_3996_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4005_, 4, v_diag_3997_);
                    v___x_4003_ = v_reuseFailAlloc_4005_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___x_4004_ = lean_st_ref_set(v___y_3947_, v___x_4003_);
                v___y_3830_ = v___x_3962_;
                v___y_3831_ = v___y_3946_;
                v___y_3832_ = v___y_3947_;
                v___y_3833_ = v___y_3948_;
                v___y_3834_ = v___y_3949_;
                state = 1;
                continue;
            }
            23 => {
                if v_isShared_4017_ == 0 {
                    v___x_4019_ = v___x_4016_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4020_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4020_, 0, v_a_4014_);
                    v___x_4019_ = v_reuseFailAlloc_4020_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_4019_;
            }
            25 => {
                v___x_4027_ = lean_st_ref_get(v___y_4026_);
                v_env_4028_ = crate::leanh::lean_ctor_get(v___x_4027_, 0);
                crate::leanh::lean_inc_ref(v_env_4028_);
                crate::leanh::lean_dec(v___x_4027_);
                crate::leanh::lean_inc(v_indName_3823_);
                v___x_4029_ = l_Lean_isMarkedMeta(v_env_4028_, v_indName_3823_);
                if v___x_4029_ == 0 {
                    v___y_3946_ = v___y_4023_;
                    v___y_3947_ = v___y_4024_;
                    v___y_3948_ = v___y_4025_;
                    v___y_3949_ = v___y_4026_;
                    state = 14;
                    continue;
                } else {
                    v___x_4030_ = lean_st_ref_take(v___y_4026_);
                    v_env_4031_ = crate::leanh::lean_ctor_get(v___x_4030_, 0);
                    v_nextMacroScope_4032_ = crate::leanh::lean_ctor_get(v___x_4030_, 1);
                    v_ngen_4033_ = crate::leanh::lean_ctor_get(v___x_4030_, 2);
                    v_auxDeclNGen_4034_ = crate::leanh::lean_ctor_get(v___x_4030_, 3);
                    v_traceState_4035_ = crate::leanh::lean_ctor_get(v___x_4030_, 4);
                    v_messages_4036_ = crate::leanh::lean_ctor_get(v___x_4030_, 6);
                    v_infoState_4037_ = crate::leanh::lean_ctor_get(v___x_4030_, 7);
                    v_snapshotTasks_4038_ = crate::leanh::lean_ctor_get(v___x_4030_, 8);
                    v_isSharedCheck_4063_ = (!crate::leanh::lean_is_exclusive(v___x_4030_)) as u8;
                    if v_isSharedCheck_4063_ == 0 {
                        v_unused_4064_ = crate::leanh::lean_ctor_get(v___x_4030_, 5);
                        crate::leanh::lean_dec(v_unused_4064_);
                        v___x_4040_ = v___x_4030_;
                        v_isShared_4041_ = v_isSharedCheck_4063_;
                        state = 26;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snapshotTasks_4038_);
                        crate::leanh::lean_inc(v_infoState_4037_);
                        crate::leanh::lean_inc(v_messages_4036_);
                        crate::leanh::lean_inc(v_traceState_4035_);
                        crate::leanh::lean_inc(v_auxDeclNGen_4034_);
                        crate::leanh::lean_inc(v_ngen_4033_);
                        crate::leanh::lean_inc(v_nextMacroScope_4032_);
                        crate::leanh::lean_inc(v_env_4031_);
                        crate::leanh::lean_dec(v___x_4030_);
                        v___x_4040_ = crate::leanh::lean_box(0);
                        v_isShared_4041_ = v_isSharedCheck_4063_;
                        state = 26;
                        continue;
                    }
                }
            }
            26 => {
                crate::leanh::lean_inc(v___x_3821_);
                v___x_4042_ = l_Lean_markMeta(v_env_4031_, v___x_3821_);
                v___x_4043_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once
                    ),
                    _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2,
                );
                if v_isShared_4041_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4040_, 5, v___x_4043_);
                    crate::leanh::lean_ctor_set(v___x_4040_, 0, v___x_4042_);
                    v___x_4045_ = v___x_4040_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_4062_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 0, v___x_4042_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 1, v_nextMacroScope_4032_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 2, v_ngen_4033_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 3, v_auxDeclNGen_4034_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 4, v_traceState_4035_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 5, v___x_4043_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 6, v_messages_4036_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 7, v_infoState_4037_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 8, v_snapshotTasks_4038_);
                    v___x_4045_ = v_reuseFailAlloc_4062_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                v___x_4046_ = lean_st_ref_set(v___y_4026_, v___x_4045_);
                v___x_4047_ = lean_st_ref_take(v___y_4024_);
                v_mctx_4048_ = crate::leanh::lean_ctor_get(v___x_4047_, 0);
                v_zetaDeltaFVarIds_4049_ = crate::leanh::lean_ctor_get(v___x_4047_, 2);
                v_postponed_4050_ = crate::leanh::lean_ctor_get(v___x_4047_, 3);
                v_diag_4051_ = crate::leanh::lean_ctor_get(v___x_4047_, 4);
                v_isSharedCheck_4060_ = (!crate::leanh::lean_is_exclusive(v___x_4047_)) as u8;
                if v_isSharedCheck_4060_ == 0 {
                    v_unused_4061_ = crate::leanh::lean_ctor_get(v___x_4047_, 1);
                    crate::leanh::lean_dec(v_unused_4061_);
                    v___x_4053_ = v___x_4047_;
                    v_isShared_4054_ = v_isSharedCheck_4060_;
                    state = 28;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_4051_);
                    crate::leanh::lean_inc(v_postponed_4050_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_4049_);
                    crate::leanh::lean_inc(v_mctx_4048_);
                    crate::leanh::lean_dec(v___x_4047_);
                    v___x_4053_ = crate::leanh::lean_box(0);
                    v_isShared_4054_ = v_isSharedCheck_4060_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___x_4055_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once
                    ),
                    _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3,
                );
                if v_isShared_4054_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4053_, 1, v___x_4055_);
                    v___x_4057_ = v___x_4053_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_4059_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_mctx_4048_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4059_, 1, v___x_4055_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4059_,
                        2,
                        v_zetaDeltaFVarIds_4049_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4059_, 3, v_postponed_4050_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4059_, 4, v_diag_4051_);
                    v___x_4057_ = v_reuseFailAlloc_4059_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                v___x_4058_ = lean_st_ref_set(v___y_4024_, v___x_4057_);
                v___y_3946_ = v___y_4023_;
                v___y_3947_ = v___y_4024_;
                v___y_3948_ = v___y_4025_;
                v___y_3949_ = v___y_4026_;
                state = 14;
                continue;
            }
            30 => {
                crate::leanh::lean_inc(v___x_3821_);
                v___x_4078_ = l_Lean_Meta_addToCompletionBlackList(v_env_4067_, v___x_3821_);
                v___x_4079_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once
                    ),
                    _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2,
                );
                if v_isShared_4077_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4076_, 5, v___x_4079_);
                    crate::leanh::lean_ctor_set(v___x_4076_, 0, v___x_4078_);
                    v___x_4081_ = v___x_4076_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_4136_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 0, v___x_4078_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 1, v_nextMacroScope_4068_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 2, v_ngen_4069_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 3, v_auxDeclNGen_4070_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 4, v_traceState_4071_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 5, v___x_4079_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 6, v_messages_4072_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 7, v_infoState_4073_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 8, v_snapshotTasks_4074_);
                    v___x_4081_ = v_reuseFailAlloc_4136_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                v___x_4082_ = lean_st_ref_set(v___y_3827_, v___x_4081_);
                v___x_4083_ = lean_st_ref_take(v___y_3825_);
                v_mctx_4084_ = crate::leanh::lean_ctor_get(v___x_4083_, 0);
                v_zetaDeltaFVarIds_4085_ = crate::leanh::lean_ctor_get(v___x_4083_, 2);
                v_postponed_4086_ = crate::leanh::lean_ctor_get(v___x_4083_, 3);
                v_diag_4087_ = crate::leanh::lean_ctor_get(v___x_4083_, 4);
                v_isSharedCheck_4134_ = (!crate::leanh::lean_is_exclusive(v___x_4083_)) as u8;
                if v_isSharedCheck_4134_ == 0 {
                    v_unused_4135_ = crate::leanh::lean_ctor_get(v___x_4083_, 1);
                    crate::leanh::lean_dec(v_unused_4135_);
                    v___x_4089_ = v___x_4083_;
                    v_isShared_4090_ = v_isSharedCheck_4134_;
                    state = 32;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_4087_);
                    crate::leanh::lean_inc(v_postponed_4086_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_4085_);
                    crate::leanh::lean_inc(v_mctx_4084_);
                    crate::leanh::lean_dec(v___x_4083_);
                    v___x_4089_ = crate::leanh::lean_box(0);
                    v_isShared_4090_ = v_isSharedCheck_4134_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                v___x_4091_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once
                    ),
                    _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3,
                );
                if v_isShared_4090_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4089_, 1, v___x_4091_);
                    v___x_4093_ = v___x_4089_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_4133_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_mctx_4084_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4133_, 1, v___x_4091_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4133_,
                        2,
                        v_zetaDeltaFVarIds_4085_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4133_, 3, v_postponed_4086_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4133_, 4, v_diag_4087_);
                    v___x_4093_ = v_reuseFailAlloc_4133_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                v___x_4094_ = lean_st_ref_set(v___y_3825_, v___x_4093_);
                v___x_4095_ = lean_st_ref_take(v___y_3827_);
                v_env_4096_ = crate::leanh::lean_ctor_get(v___x_4095_, 0);
                v_nextMacroScope_4097_ = crate::leanh::lean_ctor_get(v___x_4095_, 1);
                v_ngen_4098_ = crate::leanh::lean_ctor_get(v___x_4095_, 2);
                v_auxDeclNGen_4099_ = crate::leanh::lean_ctor_get(v___x_4095_, 3);
                v_traceState_4100_ = crate::leanh::lean_ctor_get(v___x_4095_, 4);
                v_messages_4101_ = crate::leanh::lean_ctor_get(v___x_4095_, 6);
                v_infoState_4102_ = crate::leanh::lean_ctor_get(v___x_4095_, 7);
                v_snapshotTasks_4103_ = crate::leanh::lean_ctor_get(v___x_4095_, 8);
                v_isSharedCheck_4131_ = (!crate::leanh::lean_is_exclusive(v___x_4095_)) as u8;
                if v_isSharedCheck_4131_ == 0 {
                    v_unused_4132_ = crate::leanh::lean_ctor_get(v___x_4095_, 5);
                    crate::leanh::lean_dec(v_unused_4132_);
                    v___x_4105_ = v___x_4095_;
                    v_isShared_4106_ = v_isSharedCheck_4131_;
                    state = 34;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4103_);
                    crate::leanh::lean_inc(v_infoState_4102_);
                    crate::leanh::lean_inc(v_messages_4101_);
                    crate::leanh::lean_inc(v_traceState_4100_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4099_);
                    crate::leanh::lean_inc(v_ngen_4098_);
                    crate::leanh::lean_inc(v_nextMacroScope_4097_);
                    crate::leanh::lean_inc(v_env_4096_);
                    crate::leanh::lean_dec(v___x_4095_);
                    v___x_4105_ = crate::leanh::lean_box(0);
                    v_isShared_4106_ = v_isSharedCheck_4131_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                crate::leanh::lean_inc(v___x_3821_);
                v___x_4107_ = l_Lean_addProtected(v_env_4096_, v___x_3821_);
                if v_isShared_4106_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4105_, 5, v___x_4079_);
                    crate::leanh::lean_ctor_set(v___x_4105_, 0, v___x_4107_);
                    v___x_4109_ = v___x_4105_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_4130_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4130_, 0, v___x_4107_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4130_, 1, v_nextMacroScope_4097_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4130_, 2, v_ngen_4098_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4130_, 3, v_auxDeclNGen_4099_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4130_, 4, v_traceState_4100_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4130_, 5, v___x_4079_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4130_, 6, v_messages_4101_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4130_, 7, v_infoState_4102_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4130_, 8, v_snapshotTasks_4103_);
                    v___x_4109_ = v_reuseFailAlloc_4130_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_4110_ = lean_st_ref_set(v___y_3827_, v___x_4109_);
                v___x_4111_ = lean_st_ref_take(v___y_3825_);
                v_mctx_4112_ = crate::leanh::lean_ctor_get(v___x_4111_, 0);
                v_zetaDeltaFVarIds_4113_ = crate::leanh::lean_ctor_get(v___x_4111_, 2);
                v_postponed_4114_ = crate::leanh::lean_ctor_get(v___x_4111_, 3);
                v_diag_4115_ = crate::leanh::lean_ctor_get(v___x_4111_, 4);
                v_isSharedCheck_4128_ = (!crate::leanh::lean_is_exclusive(v___x_4111_)) as u8;
                if v_isSharedCheck_4128_ == 0 {
                    v_unused_4129_ = crate::leanh::lean_ctor_get(v___x_4111_, 1);
                    crate::leanh::lean_dec(v_unused_4129_);
                    v___x_4117_ = v___x_4111_;
                    v_isShared_4118_ = v_isSharedCheck_4128_;
                    state = 36;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_4115_);
                    crate::leanh::lean_inc(v_postponed_4114_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_4113_);
                    crate::leanh::lean_inc(v_mctx_4112_);
                    crate::leanh::lean_dec(v___x_4111_);
                    v___x_4117_ = crate::leanh::lean_box(0);
                    v_isShared_4118_ = v_isSharedCheck_4128_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                if v_isShared_4118_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4117_, 1, v___x_4091_);
                    v___x_4120_ = v___x_4117_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_4127_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_mctx_4112_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4127_, 1, v___x_4091_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4127_,
                        2,
                        v_zetaDeltaFVarIds_4113_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4127_, 3, v_postponed_4114_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4127_, 4, v_diag_4115_);
                    v___x_4120_ = v_reuseFailAlloc_4127_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                v___x_4121_ = lean_st_ref_set(v___y_3825_, v___x_4120_);
                v___x_4122_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4123_ = l_Lean_InductiveVal_numCtors(v_val_3814_);
                crate::leanh::lean_dec_ref(v_val_3814_);
                v___x_4124_ = lean_nat_dec_eq(v___x_4123_, v___x_4122_);
                crate::leanh::lean_dec(v___x_4123_);
                if v___x_4124_ == 0 {
                    v___y_4023_ = v___y_3824_;
                    v___y_4024_ = v___y_3825_;
                    v___y_4025_ = v___y_3826_;
                    v___y_4026_ = v___y_3827_;
                    state = 25;
                    continue;
                } else {
                    v___x_4125_ = 2;
                    crate::leanh::lean_inc(v___x_3821_);
                    v___x_4126_ = l_Lean_Meta_setInlineAttribute(
                        v___x_3821_,
                        v___x_4125_,
                        v___y_3824_,
                        v___y_3825_,
                        v___y_3826_,
                        v___y_3827_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4126_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4126_, 1);
                        v___y_4023_ = v___y_3824_;
                        v___y_4024_ = v___y_3825_;
                        v___y_4025_ = v___y_3826_;
                        v___y_4026_ = v___y_3827_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_3944_);
                        crate::leanh::lean_dec(v_a_3924_);
                        crate::leanh::lean_dec(v_indName_3823_);
                        crate::leanh::lean_dec(v_levelParams_3822_);
                        crate::leanh::lean_dec(v___x_3821_);
                        crate::leanh::lean_dec(v___x_3816_);
                        return v___x_4126_;
                    }
                }
            }
            38 => {
                if v_isShared_4144_ == 0 {
                    v___x_4146_ = v___x_4143_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_4147_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_a_4141_);
                    v___x_4146_ = v_reuseFailAlloc_4147_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_4146_;
            }
            40 => {
                if v_isShared_4152_ == 0 {
                    v___x_4154_ = v___x_4151_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_4155_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_a_4149_);
                    v___x_4154_ = v_reuseFailAlloc_4155_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_4154_;
            }
            42 => {
                if v_isShared_4160_ == 0 {
                    v___x_4162_ = v___x_4159_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_4163_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_a_4157_);
                    v___x_4162_ = v_reuseFailAlloc_4163_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_4162_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_mkCtorIdx___lam__1___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4165_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_4166_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_xs_4167_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_4168_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_4169_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_val_4170_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_4171_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_4172_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_4173_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_4174_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_ctors_4175_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_4176_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___x_4177_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_levelParams_4178_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_indName_4179_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_4180_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_4181_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_4182_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_4183_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_4184_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___x_36067__boxed_4185_: u8 = 0;
    let mut v___x_36068__boxed_4186_: u8 = 0;
    let mut v_res_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_36067__boxed_4185_ = (crate::leanh::lean_unbox(v___x_4168_) as u8);
    v___x_36068__boxed_4186_ = (crate::leanh::lean_unbox(v___x_4169_) as u8);
    v_res_4187_ = l_mkCtorIdx___lam__1(
        v___x_4165_,
        v___x_4166_,
        v_xs_4167_,
        v___x_36067__boxed_4185_,
        v___x_36068__boxed_4186_,
        v_val_4170_,
        v___x_4171_,
        v___x_4172_,
        v___x_4173_,
        v___x_4174_,
        v_ctors_4175_,
        v___x_4176_,
        v___x_4177_,
        v_levelParams_4178_,
        v_indName_4179_,
        v___y_4180_,
        v___y_4181_,
        v___y_4182_,
        v___y_4183_,
    );
    crate::leanh::lean_dec(v___y_4183_);
    crate::leanh::lean_dec_ref(v___y_4182_);
    crate::leanh::lean_dec(v___y_4181_);
    crate::leanh::lean_dec_ref(v___y_4180_);
    return v_res_4187_;
}
pub unsafe fn l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(
    mut v_bs_4188_: *mut crate::leanh::LeanObject,
    mut v_k_4189_: *mut crate::leanh::LeanObject,
    mut v___y_4190_: *mut crate::leanh::LeanObject,
    mut v___y_4191_: *mut crate::leanh::LeanObject,
    mut v___y_4192_: *mut crate::leanh::LeanObject,
    mut v___y_4193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4199_: u8 = 0;
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4203_: u8 = 0;
    let mut v_a_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4207_: u8 = 0;
    let mut v___x_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4211_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4195_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(
                    crate::leanh::lean_box(0),
                    v_bs_4188_,
                    v_k_4189_,
                    v___y_4190_,
                    v___y_4191_,
                    v___y_4192_,
                    v___y_4193_,
                );
                if crate::leanh::lean_obj_tag(v___x_4195_) == 0 {
                    v_a_4196_ = crate::leanh::lean_ctor_get(v___x_4195_, 0);
                    v_isSharedCheck_4203_ = (!crate::leanh::lean_is_exclusive(v___x_4195_)) as u8;
                    if v_isSharedCheck_4203_ == 0 {
                        v___x_4198_ = v___x_4195_;
                        v_isShared_4199_ = v_isSharedCheck_4203_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4196_);
                        crate::leanh::lean_dec(v___x_4195_);
                        v___x_4198_ = crate::leanh::lean_box(0);
                        v_isShared_4199_ = v_isSharedCheck_4203_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4204_ = crate::leanh::lean_ctor_get(v___x_4195_, 0);
                    v_isSharedCheck_4211_ = (!crate::leanh::lean_is_exclusive(v___x_4195_)) as u8;
                    if v_isSharedCheck_4211_ == 0 {
                        v___x_4206_ = v___x_4195_;
                        v_isShared_4207_ = v_isSharedCheck_4211_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4204_);
                        crate::leanh::lean_dec(v___x_4195_);
                        v___x_4206_ = crate::leanh::lean_box(0);
                        v_isShared_4207_ = v_isSharedCheck_4211_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4199_ == 0 {
                    v___x_4201_ = v___x_4198_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4202_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4202_, 0, v_a_4196_);
                    v___x_4201_ = v_reuseFailAlloc_4202_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4201_;
            }
            3 => {
                if v_isShared_4207_ == 0 {
                    v___x_4209_ = v___x_4206_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4210_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4210_, 0, v_a_4204_);
                    v___x_4209_ = v_reuseFailAlloc_4210_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4209_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg___boxed(
    mut v_bs_4212_: *mut crate::leanh::LeanObject,
    mut v_k_4213_: *mut crate::leanh::LeanObject,
    mut v___y_4214_: *mut crate::leanh::LeanObject,
    mut v___y_4215_: *mut crate::leanh::LeanObject,
    mut v___y_4216_: *mut crate::leanh::LeanObject,
    mut v___y_4217_: *mut crate::leanh::LeanObject,
    mut v___y_4218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4219_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(v_bs_4212_, v_k_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
    crate::leanh::lean_dec(v___y_4217_);
    crate::leanh::lean_dec_ref(v___y_4216_);
    crate::leanh::lean_dec(v___y_4215_);
    crate::leanh::lean_dec_ref(v___y_4214_);
    crate::leanh::lean_dec_ref(v_bs_4212_);
    return v_res_4219_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19(
    mut v_sz_4220_: usize,
    mut v_i_4221_: usize,
    mut v_bs_4222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4223_: u8 = 0;
    let mut v_v_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: u8 = 0;
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: usize = 0;
    let mut v___x_4232_: usize = 0;
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4223_ = lean_usize_dec_lt(v_i_4221_, v_sz_4220_);
                if v___x_4223_ == 0 {
                    return v_bs_4222_;
                } else {
                    v_v_4224_ = lean_array_uget(v_bs_4222_, v_i_4221_);
                    v___x_4225_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4226_ = lean_array_uset(v_bs_4222_, v_i_4221_, v___x_4225_);
                    v___x_4227_ = l_Lean_Expr_fvarId_x21(v_v_4224_);
                    crate::leanh::lean_dec(v_v_4224_);
                    v___x_4228_ = 1;
                    v___x_4229_ = crate::leanh::lean_box((v___x_4228_) as usize);
                    v___x_4230_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4230_, 0, v___x_4227_);
                    crate::leanh::lean_ctor_set(v___x_4230_, 1, v___x_4229_);
                    v___x_4231_ = 1usize;
                    v___x_4232_ = lean_usize_add(v_i_4221_, v___x_4231_);
                    v___x_4233_ = lean_array_uset(v_bs_x27_4226_, v_i_4221_, v___x_4230_);
                    v_i_4221_ = v___x_4232_;
                    v_bs_4222_ = v___x_4233_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19___boxed(
    mut v_sz_4235_: *mut crate::leanh::LeanObject,
    mut v_i_4236_: *mut crate::leanh::LeanObject,
    mut v_bs_4237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4238_: usize = 0;
    let mut v_i_boxed_4239_: usize = 0;
    let mut v_res_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4238_ = crate::leanh::lean_unbox_usize(v_sz_4235_);
    crate::leanh::lean_dec(v_sz_4235_);
    v_i_boxed_4239_ = crate::leanh::lean_unbox_usize(v_i_4236_);
    crate::leanh::lean_dec(v_i_4236_);
    v_res_4240_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19(v_sz_boxed_4238_, v_i_boxed_4239_, v_bs_4237_);
    return v_res_4240_;
}
pub unsafe fn l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg(
    mut v_bs_4241_: *mut crate::leanh::LeanObject,
    mut v_k_4242_: *mut crate::leanh::LeanObject,
    mut v___y_4243_: *mut crate::leanh::LeanObject,
    mut v___y_4244_: *mut crate::leanh::LeanObject,
    mut v___y_4245_: *mut crate::leanh::LeanObject,
    mut v___y_4246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_4248_: usize = 0;
    let mut v___x_4249_: usize = 0;
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_4248_ = lean_array_size(v_bs_4241_);
    v___x_4249_ = 0usize;
    v___x_4250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19(v_sz_4248_, v___x_4249_, v_bs_4241_);
    v___x_4251_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(v___x_4250_, v_k_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_);
    crate::leanh::lean_dec_ref(v___x_4250_);
    return v___x_4251_;
}
pub unsafe fn l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg___boxed(
    mut v_bs_4252_: *mut crate::leanh::LeanObject,
    mut v_k_4253_: *mut crate::leanh::LeanObject,
    mut v___y_4254_: *mut crate::leanh::LeanObject,
    mut v___y_4255_: *mut crate::leanh::LeanObject,
    mut v___y_4256_: *mut crate::leanh::LeanObject,
    mut v___y_4257_: *mut crate::leanh::LeanObject,
    mut v___y_4258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4259_ = l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg(
        v_bs_4252_,
        v_k_4253_,
        v___y_4254_,
        v___y_4255_,
        v___y_4256_,
        v___y_4257_,
    );
    crate::leanh::lean_dec(v___y_4257_);
    crate::leanh::lean_dec_ref(v___y_4256_);
    crate::leanh::lean_dec(v___y_4255_);
    crate::leanh::lean_dec_ref(v___y_4254_);
    return v_res_4259_;
}
pub unsafe fn l_mkCtorIdx___lam__2(
    mut v_numParams_4263_: *mut crate::leanh::LeanObject,
    mut v_indName_4264_: *mut crate::leanh::LeanObject,
    mut v___x_4265_: *mut crate::leanh::LeanObject,
    mut v___x_4266_: *mut crate::leanh::LeanObject,
    mut v___x_4267_: u8,
    mut v___x_4268_: u8,
    mut v_val_4269_: *mut crate::leanh::LeanObject,
    mut v___x_4270_: *mut crate::leanh::LeanObject,
    mut v_ctors_4271_: *mut crate::leanh::LeanObject,
    mut v___x_4272_: *mut crate::leanh::LeanObject,
    mut v_levelParams_4273_: *mut crate::leanh::LeanObject,
    mut v_xs_4274_: *mut crate::leanh::LeanObject,
    mut v_x_4275_: *mut crate::leanh::LeanObject,
    mut v___y_4276_: *mut crate::leanh::LeanObject,
    mut v___y_4277_: *mut crate::leanh::LeanObject,
    mut v___y_4278_: *mut crate::leanh::LeanObject,
    mut v___y_4279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4281_ = crate::leanh::lean_unsigned_to_nat(0);
    crate::leanh::lean_inc(v_numParams_4263_);
    crate::leanh::lean_inc_ref_n(v_xs_4274_, 3);
    v___x_4282_ = l_Array_toSubarray___redArg(v_xs_4274_, v___x_4281_, v_numParams_4263_);
    v___x_4283_ = l_Subarray_copy___redArg(v___x_4282_);
    v___x_4284_ = lean_array_get_size(v_xs_4274_);
    v___x_4285_ = l_Array_toSubarray___redArg(v_xs_4274_, v_numParams_4263_, v___x_4284_);
    v___x_4286_ = l_Subarray_copy___redArg(v___x_4285_);
    crate::leanh::lean_inc(v___x_4265_);
    crate::leanh::lean_inc(v_indName_4264_);
    v___x_4287_ = l_Lean_mkConst(v_indName_4264_, v___x_4265_);
    v___x_4288_ = l_Lean_mkAppN(v___x_4287_, v_xs_4274_);
    v___x_4289_ = l_mkCtorIdx___lam__2___closed__1;
    v___x_4290_ = l_Lean_mkConst(v___x_4289_, v___x_4266_);
    v___x_4291_ = crate::leanh::lean_box((v___x_4267_) as usize);
    v___x_4292_ = crate::leanh::lean_box((v___x_4268_) as usize);
    v___f_4293_ = crate::leanh::lean_alloc_closure(
        l_mkCtorIdx___lam__1___boxed as *mut core::ffi::c_void,
        20,
        15,
    );
    crate::leanh::lean_closure_set(v___f_4293_, 0, v___x_4288_);
    crate::leanh::lean_closure_set(v___f_4293_, 1, v___x_4290_);
    crate::leanh::lean_closure_set(v___f_4293_, 2, v_xs_4274_);
    crate::leanh::lean_closure_set(v___f_4293_, 3, v___x_4291_);
    crate::leanh::lean_closure_set(v___f_4293_, 4, v___x_4292_);
    crate::leanh::lean_closure_set(v___f_4293_, 5, v_val_4269_);
    crate::leanh::lean_closure_set(v___f_4293_, 6, v___x_4286_);
    crate::leanh::lean_closure_set(v___f_4293_, 7, v___x_4265_);
    crate::leanh::lean_closure_set(v___f_4293_, 8, v___x_4270_);
    crate::leanh::lean_closure_set(v___f_4293_, 9, v___x_4283_);
    crate::leanh::lean_closure_set(v___f_4293_, 10, v_ctors_4271_);
    crate::leanh::lean_closure_set(v___f_4293_, 11, v___x_4281_);
    crate::leanh::lean_closure_set(v___f_4293_, 12, v___x_4272_);
    crate::leanh::lean_closure_set(v___f_4293_, 13, v_levelParams_4273_);
    crate::leanh::lean_closure_set(v___f_4293_, 14, v_indName_4264_);
    v___x_4294_ = l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg(
        v_xs_4274_,
        v___f_4293_,
        v___y_4276_,
        v___y_4277_,
        v___y_4278_,
        v___y_4279_,
    );
    return v___x_4294_;
}
pub unsafe fn l_mkCtorIdx___lam__2___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_numParams_4295_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_indName_4296_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_4297_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_4298_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_4299_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_4300_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_val_4301_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_4302_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_ctors_4303_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_4304_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_levelParams_4305_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_xs_4306_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_x_4307_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_4308_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_4309_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_4310_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_4311_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_4312_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___x_36755__boxed_4313_: u8 = 0;
    let mut v___x_36756__boxed_4314_: u8 = 0;
    let mut v_res_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_36755__boxed_4313_ = (crate::leanh::lean_unbox(v___x_4299_) as u8);
    v___x_36756__boxed_4314_ = (crate::leanh::lean_unbox(v___x_4300_) as u8);
    v_res_4315_ = l_mkCtorIdx___lam__2(
        v_numParams_4295_,
        v_indName_4296_,
        v___x_4297_,
        v___x_4298_,
        v___x_36755__boxed_4313_,
        v___x_36756__boxed_4314_,
        v_val_4301_,
        v___x_4302_,
        v_ctors_4303_,
        v___x_4304_,
        v_levelParams_4305_,
        v_xs_4306_,
        v_x_4307_,
        v___y_4308_,
        v___y_4309_,
        v___y_4310_,
        v___y_4311_,
    );
    crate::leanh::lean_dec(v___y_4311_);
    crate::leanh::lean_dec_ref(v___y_4310_);
    crate::leanh::lean_dec(v___y_4309_);
    crate::leanh::lean_dec_ref(v___y_4308_);
    crate::leanh::lean_dec_ref(v_x_4307_);
    return v_res_4315_;
}
pub unsafe fn l_List_mapTR_loop___at___00mkCtorIdx_spec__3(
    mut v_a_4316_: *mut crate::leanh::LeanObject,
    mut v_a_4317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4323_: u8 = 0;
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4329_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4316_) == 0 {
                    v___x_4318_ = l_List_reverse___redArg(v_a_4317_);
                    return v___x_4318_;
                } else {
                    v_head_4319_ = crate::leanh::lean_ctor_get(v_a_4316_, 0);
                    v_tail_4320_ = crate::leanh::lean_ctor_get(v_a_4316_, 1);
                    v_isSharedCheck_4329_ = (!crate::leanh::lean_is_exclusive(v_a_4316_)) as u8;
                    if v_isSharedCheck_4329_ == 0 {
                        v___x_4322_ = v_a_4316_;
                        v_isShared_4323_ = v_isSharedCheck_4329_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4320_);
                        crate::leanh::lean_inc(v_head_4319_);
                        crate::leanh::lean_dec(v_a_4316_);
                        v___x_4322_ = crate::leanh::lean_box(0);
                        v_isShared_4323_ = v_isSharedCheck_4329_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4324_ = l_Lean_mkLevelParam(v_head_4319_);
                if v_isShared_4323_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4322_, 1, v_a_4317_);
                    crate::leanh::lean_ctor_set(v___x_4322_, 0, v___x_4324_);
                    v___x_4326_ = v___x_4322_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4328_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4328_, 0, v___x_4324_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4328_, 1, v_a_4317_);
                    v___x_4326_ = v_reuseFailAlloc_4328_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4316_ = v_tail_4320_;
                v_a_4317_ = v___x_4326_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_mkCtorIdx___lam__3___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4332_ = l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__6;
    v___x_4333_ = crate::leanh::lean_unsigned_to_nat(62);
    v___x_4334_ = crate::leanh::lean_unsigned_to_nat(48);
    v___x_4335_ = l_mkCtorIdx___lam__3___closed__1;
    v___x_4336_ = l_mkCtorIdx___lam__3___closed__0;
    v___x_4337_ = l_mkPanicMessageWithDecl(
        v___x_4336_,
        v___x_4335_,
        v___x_4334_,
        v___x_4333_,
        v___x_4332_,
    );
    return v___x_4337_;
}
pub unsafe fn l_mkCtorIdx___lam__3(
    mut v_indName_4338_: *mut crate::leanh::LeanObject,
    mut v___x_4339_: u8,
    mut v___y_4340_: *mut crate::leanh::LeanObject,
    mut v___y_4341_: *mut crate::leanh::LeanObject,
    mut v___y_4342_: *mut crate::leanh::LeanObject,
    mut v___y_4343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: u8 = 0;
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4355_: u8 = 0;
    let mut v___x_4356_: u8 = 0;
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4362_: u8 = 0;
    let mut v_toConstantVal_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4373_: u8 = 0;
    let mut v___x_4374_: u8 = 0;
    let mut v___x_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4380_: u8 = 0;
    let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: u8 = 0;
    let mut v___x_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4399_: u8 = 0;
    let mut v_a_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4403_: u8 = 0;
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4407_: u8 = 0;
    let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4412_: u8 = 0;
    let mut v_a_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4416_: u8 = 0;
    let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4420_: u8 = 0;
    let mut v_isSharedCheck_4421_: u8 = 0;
    let mut v___x_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4427_: u8 = 0;
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4431_: u8 = 0;
    let mut v___x_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4436_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_4345_ = crate::leanh::lean_ctor_get(v___y_4342_, 2);
                v___x_4346_ = l___private_Lean_Meta_Constructions_CtorIdx_0__genCtorIdx;
                v___x_4347_ =
                    l_Lean_Option_get___at___00mkCtorIdx_spec__0(v_options_4345_, v___x_4346_);
                if v___x_4347_ == 0 {
                    crate::leanh::lean_dec(v_indName_4338_);
                    v___x_4348_ = crate::leanh::lean_box(0);
                    v___x_4349_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4349_, 0, v___x_4348_);
                    return v___x_4349_;
                } else {
                    crate::leanh::lean_inc(v_indName_4338_);
                    v___x_4350_ = l_mkCtorIdxName(v_indName_4338_);
                    crate::leanh::lean_inc(v___x_4350_);
                    v___x_4351_ = l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg(
                        v___x_4350_,
                        v___x_4347_,
                        v___y_4343_,
                    );
                    v_a_4352_ = crate::leanh::lean_ctor_get(v___x_4351_, 0);
                    v_isSharedCheck_4436_ = (!crate::leanh::lean_is_exclusive(v___x_4351_)) as u8;
                    if v_isSharedCheck_4436_ == 0 {
                        v___x_4354_ = v___x_4351_;
                        v_isShared_4355_ = v_isSharedCheck_4436_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4352_);
                        crate::leanh::lean_dec(v___x_4351_);
                        v___x_4354_ = crate::leanh::lean_box(0);
                        v_isShared_4355_ = v_isSharedCheck_4436_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4356_ = (crate::leanh::lean_unbox(v_a_4352_) as u8);
                crate::leanh::lean_dec(v_a_4352_);
                if v___x_4356_ == 0 {
                    crate::leanh::lean_del_object(v___x_4354_);
                    crate::leanh::lean_inc(v_indName_4338_);
                    v___x_4357_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(
                        v_indName_4338_,
                        v___y_4340_,
                        v___y_4341_,
                        v___y_4342_,
                        v___y_4343_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4357_) == 0 {
                        v_a_4358_ = crate::leanh::lean_ctor_get(v___x_4357_, 0);
                        crate::leanh::lean_inc(v_a_4358_);
                        crate::leanh::lean_dec_ref_known(v___x_4357_, 1);
                        if crate::leanh::lean_obj_tag(v_a_4358_) == 5 {
                            v_val_4359_ = crate::leanh::lean_ctor_get(v_a_4358_, 0);
                            v_isSharedCheck_4421_ =
                                (!crate::leanh::lean_is_exclusive(v_a_4358_)) as u8;
                            if v_isSharedCheck_4421_ == 0 {
                                v___x_4361_ = v_a_4358_;
                                v_isShared_4362_ = v_isSharedCheck_4421_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_4359_);
                                crate::leanh::lean_dec(v_a_4358_);
                                v___x_4361_ = crate::leanh::lean_box(0);
                                v_isShared_4362_ = v_isSharedCheck_4421_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4358_);
                            crate::leanh::lean_dec(v___x_4350_);
                            crate::leanh::lean_dec(v_indName_4338_);
                            v___x_4422_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_mkCtorIdx___lam__3___closed__2),
                                core::ptr::addr_of_mut!(l_mkCtorIdx___lam__3___closed__2_once),
                                _init_l_mkCtorIdx___lam__3___closed__2,
                            );
                            v___x_4423_ = l_panic___at___00mkCtorIdx_spec__13(
                                v___x_4422_,
                                v___y_4340_,
                                v___y_4341_,
                                v___y_4342_,
                                v___y_4343_,
                            );
                            return v___x_4423_;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4350_);
                        crate::leanh::lean_dec(v_indName_4338_);
                        v_a_4424_ = crate::leanh::lean_ctor_get(v___x_4357_, 0);
                        v_isSharedCheck_4431_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4357_)) as u8;
                        if v_isSharedCheck_4431_ == 0 {
                            v___x_4426_ = v___x_4357_;
                            v_isShared_4427_ = v_isSharedCheck_4431_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4424_);
                            crate::leanh::lean_dec(v___x_4357_);
                            v___x_4426_ = crate::leanh::lean_box(0);
                            v_isShared_4427_ = v_isSharedCheck_4431_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4350_);
                    crate::leanh::lean_dec(v_indName_4338_);
                    v___x_4432_ = crate::leanh::lean_box(0);
                    if v_isShared_4355_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4354_, 0, v___x_4432_);
                        v___x_4434_ = v___x_4354_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_4435_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4435_, 0, v___x_4432_);
                        v___x_4434_ = v_reuseFailAlloc_4435_;
                        state = 14;
                        continue;
                    }
                }
            }
            2 => {
                v_toConstantVal_4363_ = crate::leanh::lean_ctor_get(v_val_4359_, 0);
                v_numParams_4364_ = crate::leanh::lean_ctor_get(v_val_4359_, 1);
                crate::leanh::lean_inc(v_numParams_4364_);
                v_numIndices_4365_ = crate::leanh::lean_ctor_get(v_val_4359_, 2);
                crate::leanh::lean_inc(v_numIndices_4365_);
                v_ctors_4366_ = crate::leanh::lean_ctor_get(v_val_4359_, 4);
                crate::leanh::lean_inc(v_ctors_4366_);
                v_levelParams_4367_ = crate::leanh::lean_ctor_get(v_toConstantVal_4363_, 1);
                crate::leanh::lean_inc(v_levelParams_4367_);
                v_type_4368_ = crate::leanh::lean_ctor_get(v_toConstantVal_4363_, 2);
                crate::leanh::lean_inc_ref_n(v_type_4368_, 2);
                v___x_4369_ = l_Lean_Meta_isPropFormerType(
                    v_type_4368_,
                    v___y_4340_,
                    v___y_4341_,
                    v___y_4342_,
                    v___y_4343_,
                );
                if crate::leanh::lean_obj_tag(v___x_4369_) == 0 {
                    v_a_4370_ = crate::leanh::lean_ctor_get(v___x_4369_, 0);
                    v_isSharedCheck_4412_ = (!crate::leanh::lean_is_exclusive(v___x_4369_)) as u8;
                    if v_isSharedCheck_4412_ == 0 {
                        v___x_4372_ = v___x_4369_;
                        v_isShared_4373_ = v_isSharedCheck_4412_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4370_);
                        crate::leanh::lean_dec(v___x_4369_);
                        v___x_4372_ = crate::leanh::lean_box(0);
                        v_isShared_4373_ = v_isSharedCheck_4412_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_4368_);
                    crate::leanh::lean_dec(v_levelParams_4367_);
                    crate::leanh::lean_dec(v_ctors_4366_);
                    crate::leanh::lean_dec(v_numIndices_4365_);
                    crate::leanh::lean_dec(v_numParams_4364_);
                    crate::leanh::lean_del_object(v___x_4361_);
                    crate::leanh::lean_dec_ref(v_val_4359_);
                    crate::leanh::lean_dec(v___x_4350_);
                    crate::leanh::lean_dec(v_indName_4338_);
                    v_a_4413_ = crate::leanh::lean_ctor_get(v___x_4369_, 0);
                    v_isSharedCheck_4420_ = (!crate::leanh::lean_is_exclusive(v___x_4369_)) as u8;
                    if v_isSharedCheck_4420_ == 0 {
                        v___x_4415_ = v___x_4369_;
                        v_isShared_4416_ = v_isSharedCheck_4420_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4413_);
                        crate::leanh::lean_dec(v___x_4369_);
                        v___x_4415_ = crate::leanh::lean_box(0);
                        v_isShared_4416_ = v_isSharedCheck_4420_;
                        state = 10;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4374_ = (crate::leanh::lean_unbox(v_a_4370_) as u8);
                crate::leanh::lean_dec(v_a_4370_);
                if v___x_4374_ == 0 {
                    crate::leanh::lean_del_object(v___x_4372_);
                    crate::leanh::lean_inc(v_indName_4338_);
                    v___x_4375_ = l_Lean_mkCasesOnName(v_indName_4338_);
                    crate::leanh::lean_inc(v___x_4375_);
                    v___x_4376_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(
                        v___x_4375_,
                        v___y_4340_,
                        v___y_4341_,
                        v___y_4342_,
                        v___y_4343_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4376_) == 0 {
                        v_a_4377_ = crate::leanh::lean_ctor_get(v___x_4376_, 0);
                        v_isSharedCheck_4399_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4376_)) as u8;
                        if v_isSharedCheck_4399_ == 0 {
                            v___x_4379_ = v___x_4376_;
                            v_isShared_4380_ = v_isSharedCheck_4399_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4377_);
                            crate::leanh::lean_dec(v___x_4376_);
                            v___x_4379_ = crate::leanh::lean_box(0);
                            v_isShared_4380_ = v_isSharedCheck_4399_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4375_);
                        crate::leanh::lean_dec_ref(v_type_4368_);
                        crate::leanh::lean_dec(v_levelParams_4367_);
                        crate::leanh::lean_dec(v_ctors_4366_);
                        crate::leanh::lean_dec(v_numIndices_4365_);
                        crate::leanh::lean_dec(v_numParams_4364_);
                        crate::leanh::lean_del_object(v___x_4361_);
                        crate::leanh::lean_dec_ref(v_val_4359_);
                        crate::leanh::lean_dec(v___x_4350_);
                        crate::leanh::lean_dec(v_indName_4338_);
                        v_a_4400_ = crate::leanh::lean_ctor_get(v___x_4376_, 0);
                        v_isSharedCheck_4407_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4376_)) as u8;
                        if v_isSharedCheck_4407_ == 0 {
                            v___x_4402_ = v___x_4376_;
                            v_isShared_4403_ = v_isSharedCheck_4407_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4400_);
                            crate::leanh::lean_dec(v___x_4376_);
                            v___x_4402_ = crate::leanh::lean_box(0);
                            v_isShared_4403_ = v_isSharedCheck_4407_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_4368_);
                    crate::leanh::lean_dec(v_levelParams_4367_);
                    crate::leanh::lean_dec(v_ctors_4366_);
                    crate::leanh::lean_dec(v_numIndices_4365_);
                    crate::leanh::lean_dec(v_numParams_4364_);
                    crate::leanh::lean_del_object(v___x_4361_);
                    crate::leanh::lean_dec_ref(v_val_4359_);
                    crate::leanh::lean_dec(v___x_4350_);
                    crate::leanh::lean_dec(v_indName_4338_);
                    v___x_4408_ = crate::leanh::lean_box(0);
                    if v_isShared_4373_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4372_, 0, v___x_4408_);
                        v___x_4410_ = v___x_4372_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4411_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4411_, 0, v___x_4408_);
                        v___x_4410_ = v_reuseFailAlloc_4411_;
                        state = 9;
                        continue;
                    }
                }
            }
            4 => {
                v___x_4381_ = l_List_lengthTR___redArg(v_levelParams_4367_);
                v___x_4382_ = l_Lean_ConstantInfo_levelParams(v_a_4377_);
                crate::leanh::lean_dec(v_a_4377_);
                v___x_4383_ = l_List_lengthTR___redArg(v___x_4382_);
                crate::leanh::lean_dec(v___x_4382_);
                v___x_4384_ = lean_nat_dec_lt(v___x_4381_, v___x_4383_);
                crate::leanh::lean_dec(v___x_4383_);
                crate::leanh::lean_dec(v___x_4381_);
                if v___x_4384_ == 0 {
                    crate::leanh::lean_dec(v___x_4375_);
                    crate::leanh::lean_dec_ref(v_type_4368_);
                    crate::leanh::lean_dec(v_levelParams_4367_);
                    crate::leanh::lean_dec(v_ctors_4366_);
                    crate::leanh::lean_dec(v_numIndices_4365_);
                    crate::leanh::lean_dec(v_numParams_4364_);
                    crate::leanh::lean_del_object(v___x_4361_);
                    crate::leanh::lean_dec_ref(v_val_4359_);
                    crate::leanh::lean_dec(v___x_4350_);
                    crate::leanh::lean_dec(v_indName_4338_);
                    v___x_4385_ = crate::leanh::lean_box(0);
                    if v_isShared_4380_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4379_, 0, v___x_4385_);
                        v___x_4387_ = v___x_4379_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4388_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4388_, 0, v___x_4385_);
                        v___x_4387_ = v_reuseFailAlloc_4388_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4379_);
                    v___x_4389_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_levelParams_4367_);
                    v___x_4390_ = l_List_mapTR_loop___at___00mkCtorIdx_spec__3(
                        v_levelParams_4367_,
                        v___x_4389_,
                    );
                    v___x_4391_ = crate::leanh::lean_box((v___x_4339_) as usize);
                    v___x_4392_ = crate::leanh::lean_box((v___x_4347_) as usize);
                    crate::leanh::lean_inc(v_numParams_4364_);
                    v___f_4393_ = crate::leanh::lean_alloc_closure(
                        l_mkCtorIdx___lam__2___boxed as *mut core::ffi::c_void,
                        18,
                        11,
                    );
                    crate::leanh::lean_closure_set(v___f_4393_, 0, v_numParams_4364_);
                    crate::leanh::lean_closure_set(v___f_4393_, 1, v_indName_4338_);
                    crate::leanh::lean_closure_set(v___f_4393_, 2, v___x_4390_);
                    crate::leanh::lean_closure_set(v___f_4393_, 3, v___x_4389_);
                    crate::leanh::lean_closure_set(v___f_4393_, 4, v___x_4391_);
                    crate::leanh::lean_closure_set(v___f_4393_, 5, v___x_4392_);
                    crate::leanh::lean_closure_set(v___f_4393_, 6, v_val_4359_);
                    crate::leanh::lean_closure_set(v___f_4393_, 7, v___x_4375_);
                    crate::leanh::lean_closure_set(v___f_4393_, 8, v_ctors_4366_);
                    crate::leanh::lean_closure_set(v___f_4393_, 9, v___x_4350_);
                    crate::leanh::lean_closure_set(v___f_4393_, 10, v_levelParams_4367_);
                    v___x_4394_ = lean_nat_add(v_numParams_4364_, v_numIndices_4365_);
                    crate::leanh::lean_dec(v_numIndices_4365_);
                    crate::leanh::lean_dec(v_numParams_4364_);
                    if v_isShared_4362_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4361_, 1);
                        crate::leanh::lean_ctor_set(v___x_4361_, 0, v___x_4394_);
                        v___x_4396_ = v___x_4361_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4398_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4398_, 0, v___x_4394_);
                        v___x_4396_ = v_reuseFailAlloc_4398_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_4387_;
            }
            6 => {
                v___x_4397_ =
                    l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg(
                        v_type_4368_,
                        v___x_4396_,
                        v___f_4393_,
                        v___x_4339_,
                        v___x_4339_,
                        v___y_4340_,
                        v___y_4341_,
                        v___y_4342_,
                        v___y_4343_,
                    );
                return v___x_4397_;
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
                return v___x_4410_;
            }
            10 => {
                if v_isShared_4416_ == 0 {
                    v___x_4418_ = v___x_4415_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4419_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_a_4413_);
                    v___x_4418_ = v_reuseFailAlloc_4419_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4418_;
            }
            12 => {
                if v_isShared_4427_ == 0 {
                    v___x_4429_ = v___x_4426_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4430_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4430_, 0, v_a_4424_);
                    v___x_4429_ = v_reuseFailAlloc_4430_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4429_;
            }
            14 => {
                return v___x_4434_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_mkCtorIdx___lam__3___boxed(
    mut v_indName_4437_: *mut crate::leanh::LeanObject,
    mut v___x_4438_: *mut crate::leanh::LeanObject,
    mut v___y_4439_: *mut crate::leanh::LeanObject,
    mut v___y_4440_: *mut crate::leanh::LeanObject,
    mut v___y_4441_: *mut crate::leanh::LeanObject,
    mut v___y_4442_: *mut crate::leanh::LeanObject,
    mut v___y_4443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_36868__boxed_4444_: u8 = 0;
    let mut v_res_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_36868__boxed_4444_ = (crate::leanh::lean_unbox(v___x_4438_) as u8);
    v_res_4445_ = l_mkCtorIdx___lam__3(
        v_indName_4437_,
        v___x_36868__boxed_4444_,
        v___y_4439_,
        v___y_4440_,
        v___y_4441_,
        v___y_4442_,
    );
    crate::leanh::lean_dec(v___y_4442_);
    crate::leanh::lean_dec_ref(v___y_4441_);
    crate::leanh::lean_dec(v___y_4440_);
    crate::leanh::lean_dec_ref(v___y_4439_);
    return v_res_4445_;
}
pub unsafe fn l_mkCtorIdx___lam__4(
    mut v___x_4446_: *mut crate::leanh::LeanObject,
    mut v_e_4447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4448_ = l_Lean_indentD(v_e_4447_);
    v___x_4449_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4449_, 0, v___x_4446_);
    crate::leanh::lean_ctor_set(v___x_4449_, 1, v___x_4448_);
    return v___x_4449_;
}
pub unsafe fn l_mkCtorIdx___lam__5(
    mut v___f_4450_: *mut crate::leanh::LeanObject,
    mut v___f_4451_: *mut crate::leanh::LeanObject,
    mut v___y_4452_: *mut crate::leanh::LeanObject,
    mut v___y_4453_: *mut crate::leanh::LeanObject,
    mut v___y_4454_: *mut crate::leanh::LeanObject,
    mut v___y_4455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4461_: u8 = 0;
    let mut v___x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4465_: u8 = 0;
    let mut v_a_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4469_: u8 = 0;
    let mut v___x_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4473_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4457_ = l_Lean_Meta_mapErrorImp___redArg(
                    v___f_4450_,
                    v___f_4451_,
                    v___y_4452_,
                    v___y_4453_,
                    v___y_4454_,
                    v___y_4455_,
                );
                if crate::leanh::lean_obj_tag(v___x_4457_) == 0 {
                    v_a_4458_ = crate::leanh::lean_ctor_get(v___x_4457_, 0);
                    v_isSharedCheck_4465_ = (!crate::leanh::lean_is_exclusive(v___x_4457_)) as u8;
                    if v_isSharedCheck_4465_ == 0 {
                        v___x_4460_ = v___x_4457_;
                        v_isShared_4461_ = v_isSharedCheck_4465_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4458_);
                        crate::leanh::lean_dec(v___x_4457_);
                        v___x_4460_ = crate::leanh::lean_box(0);
                        v_isShared_4461_ = v_isSharedCheck_4465_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4466_ = crate::leanh::lean_ctor_get(v___x_4457_, 0);
                    v_isSharedCheck_4473_ = (!crate::leanh::lean_is_exclusive(v___x_4457_)) as u8;
                    if v_isSharedCheck_4473_ == 0 {
                        v___x_4468_ = v___x_4457_;
                        v_isShared_4469_ = v_isSharedCheck_4473_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4466_);
                        crate::leanh::lean_dec(v___x_4457_);
                        v___x_4468_ = crate::leanh::lean_box(0);
                        v_isShared_4469_ = v_isSharedCheck_4473_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4461_ == 0 {
                    v___x_4463_ = v___x_4460_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4464_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4464_, 0, v_a_4458_);
                    v___x_4463_ = v_reuseFailAlloc_4464_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4463_;
            }
            3 => {
                if v_isShared_4469_ == 0 {
                    v___x_4471_ = v___x_4468_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4472_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4472_, 0, v_a_4466_);
                    v___x_4471_ = v_reuseFailAlloc_4472_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4471_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_mkCtorIdx___lam__5___boxed(
    mut v___f_4474_: *mut crate::leanh::LeanObject,
    mut v___f_4475_: *mut crate::leanh::LeanObject,
    mut v___y_4476_: *mut crate::leanh::LeanObject,
    mut v___y_4477_: *mut crate::leanh::LeanObject,
    mut v___y_4478_: *mut crate::leanh::LeanObject,
    mut v___y_4479_: *mut crate::leanh::LeanObject,
    mut v___y_4480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4481_ = l_mkCtorIdx___lam__5(
        v___f_4474_,
        v___f_4475_,
        v___y_4476_,
        v___y_4477_,
        v___y_4478_,
        v___y_4479_,
    );
    crate::leanh::lean_dec(v___y_4479_);
    crate::leanh::lean_dec_ref(v___y_4478_);
    crate::leanh::lean_dec(v___y_4477_);
    crate::leanh::lean_dec_ref(v___y_4476_);
    return v_res_4481_;
}
pub unsafe fn _init_l_mkCtorIdx___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4483_ = l_mkCtorIdx___closed__0;
    v___x_4484_ = l_Lean_stringToMessageData(v___x_4483_);
    return v___x_4484_;
}
pub unsafe fn _init_l_mkCtorIdx___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4486_ = l_mkCtorIdx___closed__2;
    v___x_4487_ = l_Lean_stringToMessageData(v___x_4486_);
    return v___x_4487_;
}
pub unsafe fn l_mkCtorIdx(
    mut v_indName_4488_: *mut crate::leanh::LeanObject,
    mut v_a_4489_: *mut crate::leanh::LeanObject,
    mut v_a_4490_: *mut crate::leanh::LeanObject,
    mut v_a_4491_: *mut crate::leanh::LeanObject,
    mut v_a_4492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: u8 = 0;
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: u8 = 0;
    v___x_4494_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_mkCtorIdx___closed__1),
        core::ptr::addr_of_mut!(l_mkCtorIdx___closed__1_once),
        _init_l_mkCtorIdx___closed__1,
    );
    v___x_4495_ = 0;
    v___x_4496_ = crate::leanh::lean_box((v___x_4495_) as usize);
    crate::leanh::lean_inc_n(v_indName_4488_, 2);
    v___f_4497_ = crate::leanh::lean_alloc_closure(
        l_mkCtorIdx___lam__3___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4497_, 0, v_indName_4488_);
    crate::leanh::lean_closure_set(v___f_4497_, 1, v___x_4496_);
    v___x_4498_ = l_Lean_MessageData_ofConstName(v_indName_4488_, v___x_4495_);
    v___x_4499_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4499_, 0, v___x_4494_);
    crate::leanh::lean_ctor_set(v___x_4499_, 1, v___x_4498_);
    v___x_4500_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_mkCtorIdx___closed__3),
        core::ptr::addr_of_mut!(l_mkCtorIdx___closed__3_once),
        _init_l_mkCtorIdx___closed__3,
    );
    v___x_4501_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4501_, 0, v___x_4499_);
    crate::leanh::lean_ctor_set(v___x_4501_, 1, v___x_4500_);
    v___f_4502_ =
        crate::leanh::lean_alloc_closure(l_mkCtorIdx___lam__4 as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___f_4502_, 0, v___x_4501_);
    v___f_4503_ = crate::leanh::lean_alloc_closure(
        l_mkCtorIdx___lam__5___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___f_4503_, 0, v___f_4497_);
    crate::leanh::lean_closure_set(v___f_4503_, 1, v___f_4502_);
    v___x_4504_ = l_Lean_isPrivateName(v_indName_4488_);
    crate::leanh::lean_dec(v_indName_4488_);
    if v___x_4504_ == 0 {
        let mut v___x_4505_: u8 = 0;
        let mut v___x_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4505_ = 1;
        v___x_4506_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(
            v___f_4503_,
            v___x_4505_,
            v_a_4489_,
            v_a_4490_,
            v_a_4491_,
            v_a_4492_,
        );
        return v___x_4506_;
    } else {
        let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4507_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(
            v___f_4503_,
            v___x_4495_,
            v_a_4489_,
            v_a_4490_,
            v_a_4491_,
            v_a_4492_,
        );
        return v___x_4507_;
    }
}
pub unsafe fn l_mkCtorIdx___boxed(
    mut v_indName_4508_: *mut crate::leanh::LeanObject,
    mut v_a_4509_: *mut crate::leanh::LeanObject,
    mut v_a_4510_: *mut crate::leanh::LeanObject,
    mut v_a_4511_: *mut crate::leanh::LeanObject,
    mut v_a_4512_: *mut crate::leanh::LeanObject,
    mut v_a_4513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4514_ = l_mkCtorIdx(v_indName_4508_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_);
    crate::leanh::lean_dec(v_a_4512_);
    crate::leanh::lean_dec_ref(v_a_4511_);
    crate::leanh::lean_dec(v_a_4510_);
    crate::leanh::lean_dec_ref(v_a_4509_);
    return v_res_4514_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6(
    mut v___x_4515_: u8,
    mut v___x_4516_: *mut crate::leanh::LeanObject,
    mut v_as_4517_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4518_: *mut crate::leanh::LeanObject,
    mut v_b_4519_: *mut crate::leanh::LeanObject,
    mut v_a_4520_: *mut crate::leanh::LeanObject,
    mut v___y_4521_: *mut crate::leanh::LeanObject,
    mut v___y_4522_: *mut crate::leanh::LeanObject,
    mut v___y_4523_: *mut crate::leanh::LeanObject,
    mut v___y_4524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4526_ = l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg(
        v___x_4515_,
        v___x_4516_,
        v_as_x27_4518_,
        v_b_4519_,
        v___y_4521_,
        v___y_4522_,
        v___y_4523_,
        v___y_4524_,
    );
    return v___x_4526_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___boxed(
    mut v___x_4527_: *mut crate::leanh::LeanObject,
    mut v___x_4528_: *mut crate::leanh::LeanObject,
    mut v_as_4529_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4530_: *mut crate::leanh::LeanObject,
    mut v_b_4531_: *mut crate::leanh::LeanObject,
    mut v_a_4532_: *mut crate::leanh::LeanObject,
    mut v___y_4533_: *mut crate::leanh::LeanObject,
    mut v___y_4534_: *mut crate::leanh::LeanObject,
    mut v___y_4535_: *mut crate::leanh::LeanObject,
    mut v___y_4536_: *mut crate::leanh::LeanObject,
    mut v___y_4537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_37175__boxed_4538_: u8 = 0;
    let mut v_res_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_37175__boxed_4538_ = (crate::leanh::lean_unbox(v___x_4527_) as u8);
    v_res_4539_ = l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6(
        v___x_37175__boxed_4538_,
        v___x_4528_,
        v_as_4529_,
        v_as_x27_4530_,
        v_b_4531_,
        v_a_4532_,
        v___y_4533_,
        v___y_4534_,
        v___y_4535_,
        v___y_4536_,
    );
    crate::leanh::lean_dec(v___y_4536_);
    crate::leanh::lean_dec_ref(v___y_4535_);
    crate::leanh::lean_dec(v___y_4534_);
    crate::leanh::lean_dec_ref(v___y_4533_);
    crate::leanh::lean_dec(v_as_x27_4530_);
    crate::leanh::lean_dec(v_as_4529_);
    crate::leanh::lean_dec_ref(v___x_4528_);
    return v_res_4539_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10(
    mut v_00_u03b1_4540_: *mut crate::leanh::LeanObject,
    mut v_name_4541_: *mut crate::leanh::LeanObject,
    mut v_bi_4542_: u8,
    mut v_type_4543_: *mut crate::leanh::LeanObject,
    mut v_k_4544_: *mut crate::leanh::LeanObject,
    mut v_kind_4545_: u8,
    mut v___y_4546_: *mut crate::leanh::LeanObject,
    mut v___y_4547_: *mut crate::leanh::LeanObject,
    mut v___y_4548_: *mut crate::leanh::LeanObject,
    mut v___y_4549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4551_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(v_name_4541_, v_bi_4542_, v_type_4543_, v_k_4544_, v_kind_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_);
    return v___x_4551_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___boxed(
    mut v_00_u03b1_4552_: *mut crate::leanh::LeanObject,
    mut v_name_4553_: *mut crate::leanh::LeanObject,
    mut v_bi_4554_: *mut crate::leanh::LeanObject,
    mut v_type_4555_: *mut crate::leanh::LeanObject,
    mut v_k_4556_: *mut crate::leanh::LeanObject,
    mut v_kind_4557_: *mut crate::leanh::LeanObject,
    mut v___y_4558_: *mut crate::leanh::LeanObject,
    mut v___y_4559_: *mut crate::leanh::LeanObject,
    mut v___y_4560_: *mut crate::leanh::LeanObject,
    mut v___y_4561_: *mut crate::leanh::LeanObject,
    mut v___y_4562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_4563_: u8 = 0;
    let mut v_kind_boxed_4564_: u8 = 0;
    let mut v_res_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_4563_ = (crate::leanh::lean_unbox(v_bi_4554_) as u8);
    v_kind_boxed_4564_ = (crate::leanh::lean_unbox(v_kind_4557_) as u8);
    v_res_4565_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10(v_00_u03b1_4552_, v_name_4553_, v_bi_boxed_4563_, v_type_4555_, v_k_4556_, v_kind_boxed_4564_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_);
    crate::leanh::lean_dec(v___y_4561_);
    crate::leanh::lean_dec_ref(v___y_4560_);
    crate::leanh::lean_dec(v___y_4559_);
    crate::leanh::lean_dec_ref(v___y_4558_);
    return v_res_4565_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7(
    mut v_00_u03b1_4566_: *mut crate::leanh::LeanObject,
    mut v_name_4567_: *mut crate::leanh::LeanObject,
    mut v_type_4568_: *mut crate::leanh::LeanObject,
    mut v_k_4569_: *mut crate::leanh::LeanObject,
    mut v___y_4570_: *mut crate::leanh::LeanObject,
    mut v___y_4571_: *mut crate::leanh::LeanObject,
    mut v___y_4572_: *mut crate::leanh::LeanObject,
    mut v___y_4573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4575_ = l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg(
        v_name_4567_,
        v_type_4568_,
        v_k_4569_,
        v___y_4570_,
        v___y_4571_,
        v___y_4572_,
        v___y_4573_,
    );
    return v___x_4575_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___boxed(
    mut v_00_u03b1_4576_: *mut crate::leanh::LeanObject,
    mut v_name_4577_: *mut crate::leanh::LeanObject,
    mut v_type_4578_: *mut crate::leanh::LeanObject,
    mut v_k_4579_: *mut crate::leanh::LeanObject,
    mut v___y_4580_: *mut crate::leanh::LeanObject,
    mut v___y_4581_: *mut crate::leanh::LeanObject,
    mut v___y_4582_: *mut crate::leanh::LeanObject,
    mut v___y_4583_: *mut crate::leanh::LeanObject,
    mut v___y_4584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4585_ = l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7(
        v_00_u03b1_4576_,
        v_name_4577_,
        v_type_4578_,
        v_k_4579_,
        v___y_4580_,
        v___y_4581_,
        v___y_4582_,
        v___y_4583_,
    );
    crate::leanh::lean_dec(v___y_4583_);
    crate::leanh::lean_dec_ref(v___y_4582_);
    crate::leanh::lean_dec(v___y_4581_);
    crate::leanh::lean_dec_ref(v___y_4580_);
    return v_res_4585_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15(
    mut v_declName_4586_: *mut crate::leanh::LeanObject,
    mut v_s_4587_: u8,
    mut v___y_4588_: *mut crate::leanh::LeanObject,
    mut v___y_4589_: *mut crate::leanh::LeanObject,
    mut v___y_4590_: *mut crate::leanh::LeanObject,
    mut v___y_4591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4593_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(v_declName_4586_, v_s_4587_, v___y_4589_, v___y_4591_);
    return v___x_4593_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___boxed(
    mut v_declName_4594_: *mut crate::leanh::LeanObject,
    mut v_s_4595_: *mut crate::leanh::LeanObject,
    mut v___y_4596_: *mut crate::leanh::LeanObject,
    mut v___y_4597_: *mut crate::leanh::LeanObject,
    mut v___y_4598_: *mut crate::leanh::LeanObject,
    mut v___y_4599_: *mut crate::leanh::LeanObject,
    mut v___y_4600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_boxed_4601_: u8 = 0;
    let mut v_res_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_s_boxed_4601_ = (crate::leanh::lean_unbox(v_s_4595_) as u8);
    v_res_4602_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15(v_declName_4594_, v_s_boxed_4601_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_);
    crate::leanh::lean_dec(v___y_4599_);
    crate::leanh::lean_dec_ref(v___y_4598_);
    crate::leanh::lean_dec(v___y_4597_);
    crate::leanh::lean_dec_ref(v___y_4596_);
    return v_res_4602_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17(
    mut v_env_4603_: *mut crate::leanh::LeanObject,
    mut v___y_4604_: *mut crate::leanh::LeanObject,
    mut v___y_4605_: *mut crate::leanh::LeanObject,
    mut v___y_4606_: *mut crate::leanh::LeanObject,
    mut v___y_4607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4609_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(v_env_4603_, v___y_4605_, v___y_4607_);
    return v___x_4609_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___boxed(
    mut v_env_4610_: *mut crate::leanh::LeanObject,
    mut v___y_4611_: *mut crate::leanh::LeanObject,
    mut v___y_4612_: *mut crate::leanh::LeanObject,
    mut v___y_4613_: *mut crate::leanh::LeanObject,
    mut v___y_4614_: *mut crate::leanh::LeanObject,
    mut v___y_4615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4616_ =
        l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17(
            v_env_4610_,
            v___y_4611_,
            v___y_4612_,
            v___y_4613_,
            v___y_4614_,
        );
    crate::leanh::lean_dec(v___y_4614_);
    crate::leanh::lean_dec_ref(v___y_4613_);
    crate::leanh::lean_dec(v___y_4612_);
    crate::leanh::lean_dec_ref(v___y_4611_);
    return v_res_4616_;
}
pub unsafe fn l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20(
    mut v_00_u03b1_4617_: *mut crate::leanh::LeanObject,
    mut v_bs_4618_: *mut crate::leanh::LeanObject,
    mut v_k_4619_: *mut crate::leanh::LeanObject,
    mut v___y_4620_: *mut crate::leanh::LeanObject,
    mut v___y_4621_: *mut crate::leanh::LeanObject,
    mut v___y_4622_: *mut crate::leanh::LeanObject,
    mut v___y_4623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4625_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(v_bs_4618_, v_k_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_);
    return v___x_4625_;
}
pub unsafe fn l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___boxed(
    mut v_00_u03b1_4626_: *mut crate::leanh::LeanObject,
    mut v_bs_4627_: *mut crate::leanh::LeanObject,
    mut v_k_4628_: *mut crate::leanh::LeanObject,
    mut v___y_4629_: *mut crate::leanh::LeanObject,
    mut v___y_4630_: *mut crate::leanh::LeanObject,
    mut v___y_4631_: *mut crate::leanh::LeanObject,
    mut v___y_4632_: *mut crate::leanh::LeanObject,
    mut v___y_4633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4634_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20(v_00_u03b1_4626_, v_bs_4627_, v_k_4628_, v___y_4629_, v___y_4630_, v___y_4631_, v___y_4632_);
    crate::leanh::lean_dec(v___y_4632_);
    crate::leanh::lean_dec_ref(v___y_4631_);
    crate::leanh::lean_dec(v___y_4630_);
    crate::leanh::lean_dec_ref(v___y_4629_);
    crate::leanh::lean_dec_ref(v_bs_4627_);
    return v_res_4634_;
}
pub unsafe fn l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12(
    mut v_00_u03b1_4635_: *mut crate::leanh::LeanObject,
    mut v_bs_4636_: *mut crate::leanh::LeanObject,
    mut v_k_4637_: *mut crate::leanh::LeanObject,
    mut v___y_4638_: *mut crate::leanh::LeanObject,
    mut v___y_4639_: *mut crate::leanh::LeanObject,
    mut v___y_4640_: *mut crate::leanh::LeanObject,
    mut v___y_4641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4643_ = l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg(
        v_bs_4636_,
        v_k_4637_,
        v___y_4638_,
        v___y_4639_,
        v___y_4640_,
        v___y_4641_,
    );
    return v___x_4643_;
}
pub unsafe fn l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___boxed(
    mut v_00_u03b1_4644_: *mut crate::leanh::LeanObject,
    mut v_bs_4645_: *mut crate::leanh::LeanObject,
    mut v_k_4646_: *mut crate::leanh::LeanObject,
    mut v___y_4647_: *mut crate::leanh::LeanObject,
    mut v___y_4648_: *mut crate::leanh::LeanObject,
    mut v___y_4649_: *mut crate::leanh::LeanObject,
    mut v___y_4650_: *mut crate::leanh::LeanObject,
    mut v___y_4651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4652_ = l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12(
        v_00_u03b1_4644_,
        v_bs_4645_,
        v_k_4646_,
        v___y_4647_,
        v___y_4648_,
        v___y_4649_,
        v___y_4650_,
    );
    crate::leanh::lean_dec(v___y_4650_);
    crate::leanh::lean_dec_ref(v___y_4649_);
    crate::leanh::lean_dec(v___y_4648_);
    crate::leanh::lean_dec_ref(v___y_4647_);
    return v_res_4652_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2(
    mut v_00_u03b1_4653_: *mut crate::leanh::LeanObject,
    mut v_constName_4654_: *mut crate::leanh::LeanObject,
    mut v___y_4655_: *mut crate::leanh::LeanObject,
    mut v___y_4656_: *mut crate::leanh::LeanObject,
    mut v___y_4657_: *mut crate::leanh::LeanObject,
    mut v___y_4658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4660_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(v_constName_4654_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_);
    return v___x_4660_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___boxed(
    mut v_00_u03b1_4661_: *mut crate::leanh::LeanObject,
    mut v_constName_4662_: *mut crate::leanh::LeanObject,
    mut v___y_4663_: *mut crate::leanh::LeanObject,
    mut v___y_4664_: *mut crate::leanh::LeanObject,
    mut v___y_4665_: *mut crate::leanh::LeanObject,
    mut v___y_4666_: *mut crate::leanh::LeanObject,
    mut v___y_4667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4668_ =
        l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2(
            v_00_u03b1_4661_,
            v_constName_4662_,
            v___y_4663_,
            v___y_4664_,
            v___y_4665_,
            v___y_4666_,
        );
    crate::leanh::lean_dec(v___y_4666_);
    crate::leanh::lean_dec_ref(v___y_4665_);
    crate::leanh::lean_dec(v___y_4664_);
    crate::leanh::lean_dec_ref(v___y_4663_);
    return v_res_4668_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5(
    mut v_00_u03b1_4669_: *mut crate::leanh::LeanObject,
    mut v_msg_4670_: *mut crate::leanh::LeanObject,
    mut v___y_4671_: *mut crate::leanh::LeanObject,
    mut v___y_4672_: *mut crate::leanh::LeanObject,
    mut v___y_4673_: *mut crate::leanh::LeanObject,
    mut v___y_4674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4676_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v_msg_4670_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_);
    return v___x_4676_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___boxed(
    mut v_00_u03b1_4677_: *mut crate::leanh::LeanObject,
    mut v_msg_4678_: *mut crate::leanh::LeanObject,
    mut v___y_4679_: *mut crate::leanh::LeanObject,
    mut v___y_4680_: *mut crate::leanh::LeanObject,
    mut v___y_4681_: *mut crate::leanh::LeanObject,
    mut v___y_4682_: *mut crate::leanh::LeanObject,
    mut v___y_4683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4684_ =
        l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5(
            v_00_u03b1_4677_,
            v_msg_4678_,
            v___y_4679_,
            v___y_4680_,
            v___y_4681_,
            v___y_4682_,
        );
    crate::leanh::lean_dec(v___y_4682_);
    crate::leanh::lean_dec_ref(v___y_4681_);
    crate::leanh::lean_dec(v___y_4680_);
    crate::leanh::lean_dec_ref(v___y_4679_);
    return v_res_4684_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7(
    mut v_00_u03b1_4685_: *mut crate::leanh::LeanObject,
    mut v_ref_4686_: *mut crate::leanh::LeanObject,
    mut v_constName_4687_: *mut crate::leanh::LeanObject,
    mut v___y_4688_: *mut crate::leanh::LeanObject,
    mut v___y_4689_: *mut crate::leanh::LeanObject,
    mut v___y_4690_: *mut crate::leanh::LeanObject,
    mut v___y_4691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4693_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_4686_, v_constName_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_);
    return v___x_4693_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___boxed(
    mut v_00_u03b1_4694_: *mut crate::leanh::LeanObject,
    mut v_ref_4695_: *mut crate::leanh::LeanObject,
    mut v_constName_4696_: *mut crate::leanh::LeanObject,
    mut v___y_4697_: *mut crate::leanh::LeanObject,
    mut v___y_4698_: *mut crate::leanh::LeanObject,
    mut v___y_4699_: *mut crate::leanh::LeanObject,
    mut v___y_4700_: *mut crate::leanh::LeanObject,
    mut v___y_4701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4702_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7(v_00_u03b1_4694_, v_ref_4695_, v_constName_4696_, v___y_4697_, v___y_4698_, v___y_4699_, v___y_4700_);
    crate::leanh::lean_dec(v___y_4700_);
    crate::leanh::lean_dec_ref(v___y_4699_);
    crate::leanh::lean_dec(v___y_4698_);
    crate::leanh::lean_dec_ref(v___y_4697_);
    crate::leanh::lean_dec(v_ref_4695_);
    return v_res_4702_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21(
    mut v_00_u03b1_4703_: *mut crate::leanh::LeanObject,
    mut v_ref_4704_: *mut crate::leanh::LeanObject,
    mut v_msg_4705_: *mut crate::leanh::LeanObject,
    mut v_declHint_4706_: *mut crate::leanh::LeanObject,
    mut v___y_4707_: *mut crate::leanh::LeanObject,
    mut v___y_4708_: *mut crate::leanh::LeanObject,
    mut v___y_4709_: *mut crate::leanh::LeanObject,
    mut v___y_4710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4712_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(v_ref_4704_, v_msg_4705_, v_declHint_4706_, v___y_4707_, v___y_4708_, v___y_4709_, v___y_4710_);
    return v___x_4712_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___boxed(
    mut v_00_u03b1_4713_: *mut crate::leanh::LeanObject,
    mut v_ref_4714_: *mut crate::leanh::LeanObject,
    mut v_msg_4715_: *mut crate::leanh::LeanObject,
    mut v_declHint_4716_: *mut crate::leanh::LeanObject,
    mut v___y_4717_: *mut crate::leanh::LeanObject,
    mut v___y_4718_: *mut crate::leanh::LeanObject,
    mut v___y_4719_: *mut crate::leanh::LeanObject,
    mut v___y_4720_: *mut crate::leanh::LeanObject,
    mut v___y_4721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4722_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21(v_00_u03b1_4713_, v_ref_4714_, v_msg_4715_, v_declHint_4716_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
    crate::leanh::lean_dec(v___y_4720_);
    crate::leanh::lean_dec_ref(v___y_4719_);
    crate::leanh::lean_dec(v___y_4718_);
    crate::leanh::lean_dec_ref(v___y_4717_);
    crate::leanh::lean_dec(v_ref_4714_);
    return v_res_4722_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27(
    mut v_msg_4723_: *mut crate::leanh::LeanObject,
    mut v_declHint_4724_: *mut crate::leanh::LeanObject,
    mut v___y_4725_: *mut crate::leanh::LeanObject,
    mut v___y_4726_: *mut crate::leanh::LeanObject,
    mut v___y_4727_: *mut crate::leanh::LeanObject,
    mut v___y_4728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4730_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(v_msg_4723_, v_declHint_4724_, v___y_4728_);
    return v___x_4730_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___boxed(
    mut v_msg_4731_: *mut crate::leanh::LeanObject,
    mut v_declHint_4732_: *mut crate::leanh::LeanObject,
    mut v___y_4733_: *mut crate::leanh::LeanObject,
    mut v___y_4734_: *mut crate::leanh::LeanObject,
    mut v___y_4735_: *mut crate::leanh::LeanObject,
    mut v___y_4736_: *mut crate::leanh::LeanObject,
    mut v___y_4737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4738_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27(v_msg_4731_, v_declHint_4732_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_);
    crate::leanh::lean_dec(v___y_4736_);
    crate::leanh::lean_dec_ref(v___y_4735_);
    crate::leanh::lean_dec(v___y_4734_);
    crate::leanh::lean_dec_ref(v___y_4733_);
    return v_res_4738_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27(
    mut v_00_u03b1_4739_: *mut crate::leanh::LeanObject,
    mut v_ref_4740_: *mut crate::leanh::LeanObject,
    mut v_msg_4741_: *mut crate::leanh::LeanObject,
    mut v___y_4742_: *mut crate::leanh::LeanObject,
    mut v___y_4743_: *mut crate::leanh::LeanObject,
    mut v___y_4744_: *mut crate::leanh::LeanObject,
    mut v___y_4745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4747_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(v_ref_4740_, v_msg_4741_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_);
    return v___x_4747_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___boxed(
    mut v_00_u03b1_4748_: *mut crate::leanh::LeanObject,
    mut v_ref_4749_: *mut crate::leanh::LeanObject,
    mut v_msg_4750_: *mut crate::leanh::LeanObject,
    mut v___y_4751_: *mut crate::leanh::LeanObject,
    mut v___y_4752_: *mut crate::leanh::LeanObject,
    mut v___y_4753_: *mut crate::leanh::LeanObject,
    mut v___y_4754_: *mut crate::leanh::LeanObject,
    mut v___y_4755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4756_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27(v_00_u03b1_4748_, v_ref_4749_, v_msg_4750_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_);
    crate::leanh::lean_dec(v___y_4754_);
    crate::leanh::lean_dec_ref(v___y_4753_);
    crate::leanh::lean_dec(v___y_4752_);
    crate::leanh::lean_dec_ref(v___y_4751_);
    crate::leanh::lean_dec(v_ref_4749_);
    return v_res_4756_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Constructions_CtorIdx(
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
    res = runtime_initialize_Lean_AddDecl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CompletionName(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Deprecated(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Meta_Constructions_CtorIdx_0__genCtorIdx =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l___private_Lean_Meta_Constructions_CtorIdx_0__genCtorIdx);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Constructions_CtorIdx(
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
pub unsafe fn initialize_Lean_Meta_Constructions_CtorIdx(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Lean_AddDecl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_CompletionName(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_Deprecated(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Constructions_CtorIdx(builtin);
}
