// Lean compiler output
// Module: Lean.Meta.Constructions.CtorIdx
// Imports: Lean.Meta.Basic Lean.AddDecl Lean.Meta.CompletionName Lean.Linter.Deprecated
use crate::ffi::{
    lean_array_get, lean_array_get_size, lean_array_push, lean_array_size, lean_array_uget,
    lean_array_uset, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_lt, lean_panic_fn_borrowed, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_string_dec_eq, lean_uint32_add, lean_usize_add, lean_usize_dec_lt,
};
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
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [103, 101, 110, 67, 116, 111, 114, 73, 100, 120, 0]};
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut leanh::LeanObject,14568703005891071609 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: leanh::LeanStringObject<57> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 57, m_capacity: 57, m_length: 56, m_data: [103, 101, 110, 101, 114, 97, 116, 101, 32, 116, 104, 101, 32, 96, 67, 116, 111, 114, 73, 100, 120, 96, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 32, 102, 111, 114, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 100, 97, 116, 97, 116, 121, 112, 101, 115, 0]};
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut leanh::LeanObject,13556645696814629918 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [67, 111, 110, 115, 116, 114, 117, 99, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut leanh::LeanObject,6298619751691480032 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 116, 111, 114, 73, 100, 120, 0]};
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut leanh::LeanObject,16920199611135063957 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,14740007710918899200 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut leanh::LeanObject,8814159201242699910 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Meta_Constructions_CtorIdx_0__genCtorIdx:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_mkToCtorIdxName___closed__0_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_mkToCtorIdxName___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkToCtorIdxName___closed__0_value) as *mut leanh::LeanObject;
pub static l_mkCtorIdxName___closed__0_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_mkCtorIdxName___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkCtorIdxName___closed__0_value) as *mut leanh::LeanObject;
pub static l_panic___at___00mkCtorIdx_spec__13___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00mkCtorIdx_spec__13___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00mkCtorIdx_spec__13___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__1_value
) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__2_value
) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__3_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__3_value
) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__4_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__0_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__2_value:
    leanh::LeanStringObject<23> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__4_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__5_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__6_value:
    leanh::LeanStringObject<34> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_mkCtorIdx___lam__0___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_mkCtorIdx___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__6_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__8_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__10_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__12_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__14_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__14_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__16_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__18_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__18_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_mkCtorIdx___lam__1___closed__0_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_mkCtorIdx___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkCtorIdx___lam__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_mkCtorIdx___lam__1___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [core::ptr::addr_of!(l_mkCtorIdx___lam__1___closed__0_value)
            as *mut leanh::LeanObject],
    };
static mut l_mkCtorIdx___lam__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkCtorIdx___lam__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_mkCtorIdx___lam__1___closed__2_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_mkCtorIdx___lam__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkCtorIdx___lam__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_mkCtorIdx___lam__1___closed__3_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_mkCtorIdx___lam__1___closed__2_value)
                as *mut leanh::LeanObject,
            13655884332201764339 as *mut leanh::LeanObject,
        ],
    };
static mut l_mkCtorIdx___lam__1___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkCtorIdx___lam__1___closed__3_value) as *mut leanh::LeanObject;
pub static l_mkCtorIdx___lam__2___closed__0_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_mkCtorIdx___lam__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkCtorIdx___lam__2___closed__0_value) as *mut leanh::LeanObject;
pub static l_mkCtorIdx___lam__2___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_mkCtorIdx___lam__2___closed__0_value)
                as *mut leanh::LeanObject,
            11442535297760353691 as *mut leanh::LeanObject,
        ],
    };
static mut l_mkCtorIdx___lam__2___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkCtorIdx___lam__2___closed__1_value) as *mut leanh::LeanObject;
pub static l_mkCtorIdx___lam__3___closed__0_value: leanh::LeanStringObject<32> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_mkCtorIdx___lam__3___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkCtorIdx___lam__3___closed__0_value) as *mut leanh::LeanObject;
pub static l_mkCtorIdx___lam__3___closed__1_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_mkCtorIdx___lam__3___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkCtorIdx___lam__3___closed__1_value) as *mut leanh::LeanObject;
static mut l_mkCtorIdx___lam__3___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_mkCtorIdx___lam__3___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_mkCtorIdx___closed__0_value: leanh::LeanStringObject<38> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_mkCtorIdx___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkCtorIdx___closed__0_value) as *mut leanh::LeanObject;
static mut l_mkCtorIdx___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_mkCtorIdx___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_mkCtorIdx___closed__2_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_mkCtorIdx___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkCtorIdx___closed__2_value) as *mut leanh::LeanObject;
static mut l_mkCtorIdx___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_mkCtorIdx___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(
    mut v_name_2379_: *mut leanh::LeanObject,
    mut v_decl_2380_: *mut leanh::LeanObject,
    mut v_ref_2381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_defValue_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: u8 = 0;
    let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2392_: u8 = 0;
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2397_: u8 = 0;
    let mut v_unused_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2402_: u8 = 0;
    let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2406_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_2383_ = leanh::lean_ctor_get(v_decl_2380_, 0);
                v_descr_2384_ = leanh::lean_ctor_get(v_decl_2380_, 1);
                v_deprecation_x3f_2385_ = leanh::lean_ctor_get(v_decl_2380_, 2);
                v___x_2386_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_2387_ = (leanh::lean_unbox(v_defValue_2383_) as u8);
                leanh::lean_ctor_set_uint8(v___x_2386_, 0 as u32, v___x_2387_);
                leanh::lean_inc(v_deprecation_x3f_2385_);
                leanh::lean_inc_ref(v_descr_2384_);
                leanh::lean_inc_n(v_name_2379_, 2);
                v___x_2388_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_2388_, 0, v_name_2379_);
                leanh::lean_ctor_set(v___x_2388_, 1, v_ref_2381_);
                leanh::lean_ctor_set(v___x_2388_, 2, v___x_2386_);
                leanh::lean_ctor_set(v___x_2388_, 3, v_descr_2384_);
                leanh::lean_ctor_set(v___x_2388_, 4, v_deprecation_x3f_2385_);
                v___x_2389_ = lean_register_option(v_name_2379_, v___x_2388_);
                if leanh::lean_obj_tag(v___x_2389_) == 0 {
                    v_isSharedCheck_2397_ = (!leanh::lean_is_exclusive(v___x_2389_)) as u8;
                    if v_isSharedCheck_2397_ == 0 {
                        v_unused_2398_ = leanh::lean_ctor_get(v___x_2389_, 0);
                        leanh::lean_dec(v_unused_2398_);
                        v___x_2391_ = v___x_2389_;
                        v_isShared_2392_ = v_isSharedCheck_2397_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2389_);
                        v___x_2391_ = leanh::lean_box(0);
                        v_isShared_2392_ = v_isSharedCheck_2397_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_name_2379_);
                    v_a_2399_ = leanh::lean_ctor_get(v___x_2389_, 0);
                    v_isSharedCheck_2406_ = (!leanh::lean_is_exclusive(v___x_2389_)) as u8;
                    if v_isSharedCheck_2406_ == 0 {
                        v___x_2401_ = v___x_2389_;
                        v_isShared_2402_ = v_isSharedCheck_2406_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2399_);
                        leanh::lean_dec(v___x_2389_);
                        v___x_2401_ = leanh::lean_box(0);
                        v_isShared_2402_ = v_isSharedCheck_2406_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_defValue_2383_);
                v___x_2393_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2393_, 0, v_name_2379_);
                leanh::lean_ctor_set(v___x_2393_, 1, v_defValue_2383_);
                if v_isShared_2392_ == 0 {
                    leanh::lean_ctor_set(v___x_2391_, 0, v___x_2393_);
                    v___x_2395_ = v___x_2391_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2396_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2393_);
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
                    v_reuseFailAlloc_2405_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2399_);
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
    mut v_name_2407_: *mut leanh::LeanObject,
    mut v_decl_2408_: *mut leanh::LeanObject,
    mut v_ref_2409_: *mut leanh::LeanObject,
    mut v_a_2410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2411_ = l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(v_name_2407_, v_decl_2408_, v_ref_2409_);
    leanh::lean_dec_ref(v_decl_2408_);
    return v_res_2411_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_()
-> *mut leanh::LeanObject {
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2448_ = l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_;
    v___x_2449_ = l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_;
    v___x_2450_ = l___private_Lean_Meta_Constructions_CtorIdx_0__initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_;
    v___x_2451_ = l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(v___x_2448_, v___x_2449_, v___x_2450_);
    return v___x_2451_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4____boxed(
    mut v_a_2452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2453_ = l___private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_();
    return v_res_2453_;
}
pub unsafe fn l_mkToCtorIdxName(
    mut v_indName_2455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2456_ = l_mkToCtorIdxName___closed__0;
    v___x_2457_ = l_Lean_Name_str___override(v_indName_2455_, v___x_2456_);
    return v___x_2457_;
}
pub unsafe fn l_mkCtorIdxName(
    mut v_indName_2459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2460_ = l_mkCtorIdxName___closed__0;
    v___x_2461_ = l_Lean_Name_str___override(v_indName_2459_, v___x_2460_);
    return v___x_2461_;
}
pub unsafe fn l_isCtorIdxCore_x3f(
    mut v_env_2462_: *mut leanh::LeanObject,
    mut v_declName_2463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_declName_2463_) == 1 {
        let mut v_pre_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_str_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2467_: u8 = 0;
        v_pre_2464_ = leanh::lean_ctor_get(v_declName_2463_, 0);
        leanh::lean_inc(v_pre_2464_);
        v_str_2465_ = leanh::lean_ctor_get(v_declName_2463_, 1);
        leanh::lean_inc_ref(v_str_2465_);
        leanh::lean_dec_ref_known(v_declName_2463_, 2);
        v___x_2466_ = l_mkCtorIdxName___closed__0;
        v___x_2467_ = lean_string_dec_eq(v_str_2465_, v___x_2466_);
        leanh::lean_dec_ref(v_str_2465_);
        if v___x_2467_ == 0 {
            let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_pre_2464_);
            leanh::lean_dec_ref(v_env_2462_);
            v___x_2468_ = leanh::lean_box(0);
            return v___x_2468_;
        } else {
            let mut v___x_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2469_ = l_Lean_isInductiveCore_x3f(v_env_2462_, v_pre_2464_);
            return v___x_2469_;
        }
    } else {
        let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_declName_2463_);
        leanh::lean_dec_ref(v_env_2462_);
        v___x_2470_ = leanh::lean_box(0);
        return v___x_2470_;
    }
}
pub unsafe fn l_isCtorIdx_x3f___redArg(
    mut v_declName_2471_: *mut leanh::LeanObject,
    mut v_a_2472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2474_ = lean_st_ref_get(v_a_2472_);
    v_env_2475_ = leanh::lean_ctor_get(v___x_2474_, 0);
    leanh::lean_inc_ref(v_env_2475_);
    leanh::lean_dec(v___x_2474_);
    v___x_2476_ = l_isCtorIdxCore_x3f(v_env_2475_, v_declName_2471_);
    v___x_2477_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2477_, 0, v___x_2476_);
    return v___x_2477_;
}
pub unsafe fn l_isCtorIdx_x3f___redArg___boxed(
    mut v_declName_2478_: *mut leanh::LeanObject,
    mut v_a_2479_: *mut leanh::LeanObject,
    mut v_a_2480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2481_ = l_isCtorIdx_x3f___redArg(v_declName_2478_, v_a_2479_);
    leanh::lean_dec(v_a_2479_);
    return v_res_2481_;
}
pub unsafe fn l_isCtorIdx_x3f(
    mut v_declName_2482_: *mut leanh::LeanObject,
    mut v_a_2483_: *mut leanh::LeanObject,
    mut v_a_2484_: *mut leanh::LeanObject,
    mut v_a_2485_: *mut leanh::LeanObject,
    mut v_a_2486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2488_ = l_isCtorIdx_x3f___redArg(v_declName_2482_, v_a_2486_);
    return v___x_2488_;
}
pub unsafe fn l_isCtorIdx_x3f___boxed(
    mut v_declName_2489_: *mut leanh::LeanObject,
    mut v_a_2490_: *mut leanh::LeanObject,
    mut v_a_2491_: *mut leanh::LeanObject,
    mut v_a_2492_: *mut leanh::LeanObject,
    mut v_a_2493_: *mut leanh::LeanObject,
    mut v_a_2494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2495_ = l_isCtorIdx_x3f(v_declName_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_);
    leanh::lean_dec(v_a_2493_);
    leanh::lean_dec_ref(v_a_2492_);
    leanh::lean_dec(v_a_2491_);
    leanh::lean_dec_ref(v_a_2490_);
    return v_res_2495_;
}
pub unsafe fn l_Lean_Option_get___at___00mkCtorIdx_spec__0(
    mut v_opts_2496_: *mut leanh::LeanObject,
    mut v_opt_2497_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_2498_ = leanh::lean_ctor_get(v_opt_2497_, 0);
    v_defValue_2499_ = leanh::lean_ctor_get(v_opt_2497_, 1);
    v_map_2500_ = leanh::lean_ctor_get(v_opts_2496_, 0);
    v___x_2501_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2500_,
            v_name_2498_,
        );
    if leanh::lean_obj_tag(v___x_2501_) == 0 {
        let mut v___x_2502_: u8 = 0;
        v___x_2502_ = (leanh::lean_unbox(v_defValue_2499_) as u8);
        return v___x_2502_;
    } else {
        let mut v_val_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2503_ = leanh::lean_ctor_get(v___x_2501_, 0);
        leanh::lean_inc(v_val_2503_);
        leanh::lean_dec_ref_known(v___x_2501_, 1);
        if leanh::lean_obj_tag(v_val_2503_) == 1 {
            let mut v_v_2504_: u8 = 0;
            v_v_2504_ = leanh::lean_ctor_get_uint8(v_val_2503_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_2503_, 0);
            return v_v_2504_;
        } else {
            let mut v___x_2505_: u8 = 0;
            leanh::lean_dec(v_val_2503_);
            v___x_2505_ = (leanh::lean_unbox(v_defValue_2499_) as u8);
            return v___x_2505_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00mkCtorIdx_spec__0___boxed(
    mut v_opts_2506_: *mut leanh::LeanObject,
    mut v_opt_2507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2508_: u8 = 0;
    let mut v_r_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2508_ = l_Lean_Option_get___at___00mkCtorIdx_spec__0(v_opts_2506_, v_opt_2507_);
    leanh::lean_dec_ref(v_opt_2507_);
    leanh::lean_dec_ref(v_opts_2506_);
    v_r_2509_ = leanh::lean_box((v_res_2508_) as usize);
    return v_r_2509_;
}
pub unsafe fn l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg(
    mut v_constName_2510_: *mut leanh::LeanObject,
    mut v_skipRealize_2511_: u8,
    mut v___y_2512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: u8 = 0;
    let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2514_ = lean_st_ref_get(v___y_2512_);
    v_env_2515_ = leanh::lean_ctor_get(v___x_2514_, 0);
    leanh::lean_inc_ref(v_env_2515_);
    leanh::lean_dec(v___x_2514_);
    v___x_2516_ = l_Lean_Environment_contains(v_env_2515_, v_constName_2510_, v_skipRealize_2511_);
    v___x_2517_ = leanh::lean_box((v___x_2516_) as usize);
    v___x_2518_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2518_, 0, v___x_2517_);
    return v___x_2518_;
}
pub unsafe fn l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg___boxed(
    mut v_constName_2519_: *mut leanh::LeanObject,
    mut v_skipRealize_2520_: *mut leanh::LeanObject,
    mut v___y_2521_: *mut leanh::LeanObject,
    mut v___y_2522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipRealize_boxed_2523_: u8 = 0;
    let mut v_res_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_2523_ = (leanh::lean_unbox(v_skipRealize_2520_) as u8);
    v_res_2524_ = l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg(
        v_constName_2519_,
        v_skipRealize_boxed_2523_,
        v___y_2521_,
    );
    leanh::lean_dec(v___y_2521_);
    return v_res_2524_;
}
pub unsafe fn l_Lean_hasConst___at___00mkCtorIdx_spec__1(
    mut v_constName_2525_: *mut leanh::LeanObject,
    mut v_skipRealize_2526_: u8,
    mut v___y_2527_: *mut leanh::LeanObject,
    mut v___y_2528_: *mut leanh::LeanObject,
    mut v___y_2529_: *mut leanh::LeanObject,
    mut v___y_2530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2532_ = l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg(
        v_constName_2525_,
        v_skipRealize_2526_,
        v___y_2530_,
    );
    return v___x_2532_;
}
pub unsafe fn l_Lean_hasConst___at___00mkCtorIdx_spec__1___boxed(
    mut v_constName_2533_: *mut leanh::LeanObject,
    mut v_skipRealize_2534_: *mut leanh::LeanObject,
    mut v___y_2535_: *mut leanh::LeanObject,
    mut v___y_2536_: *mut leanh::LeanObject,
    mut v___y_2537_: *mut leanh::LeanObject,
    mut v___y_2538_: *mut leanh::LeanObject,
    mut v___y_2539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipRealize_boxed_2540_: u8 = 0;
    let mut v_res_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_2540_ = (leanh::lean_unbox(v_skipRealize_2534_) as u8);
    v_res_2541_ = l_Lean_hasConst___at___00mkCtorIdx_spec__1(
        v_constName_2533_,
        v_skipRealize_boxed_2540_,
        v___y_2535_,
        v___y_2536_,
        v___y_2537_,
        v___y_2538_,
    );
    leanh::lean_dec(v___y_2538_);
    leanh::lean_dec_ref(v___y_2537_);
    leanh::lean_dec(v___y_2536_);
    leanh::lean_dec_ref(v___y_2535_);
    return v_res_2541_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0(
    mut v_k_2542_: *mut leanh::LeanObject,
    mut v_b_2543_: *mut leanh::LeanObject,
    mut v_c_2544_: *mut leanh::LeanObject,
    mut v___y_2545_: *mut leanh::LeanObject,
    mut v___y_2546_: *mut leanh::LeanObject,
    mut v___y_2547_: *mut leanh::LeanObject,
    mut v___y_2548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_2548_);
    leanh::lean_inc_ref(v___y_2547_);
    leanh::lean_inc(v___y_2546_);
    leanh::lean_inc_ref(v___y_2545_);
    v___x_2550_ = leanh::lean_apply_7(
        v_k_2542_,
        v_b_2543_,
        v_c_2544_,
        v___y_2545_,
        v___y_2546_,
        v___y_2547_,
        v___y_2548_,
        leanh::lean_box(0),
    );
    return v___x_2550_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0___boxed(
    mut v_k_2551_: *mut leanh::LeanObject,
    mut v_b_2552_: *mut leanh::LeanObject,
    mut v_c_2553_: *mut leanh::LeanObject,
    mut v___y_2554_: *mut leanh::LeanObject,
    mut v___y_2555_: *mut leanh::LeanObject,
    mut v___y_2556_: *mut leanh::LeanObject,
    mut v___y_2557_: *mut leanh::LeanObject,
    mut v___y_2558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2559_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0(
        v_k_2551_,
        v_b_2552_,
        v_c_2553_,
        v___y_2554_,
        v___y_2555_,
        v___y_2556_,
        v___y_2557_,
    );
    leanh::lean_dec(v___y_2557_);
    leanh::lean_dec_ref(v___y_2556_);
    leanh::lean_dec(v___y_2555_);
    leanh::lean_dec_ref(v___y_2554_);
    return v_res_2559_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg(
    mut v_type_2560_: *mut leanh::LeanObject,
    mut v_maxFVars_x3f_2561_: *mut leanh::LeanObject,
    mut v_k_2562_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2563_: u8,
    mut v_whnfType_2564_: u8,
    mut v___y_2565_: *mut leanh::LeanObject,
    mut v___y_2566_: *mut leanh::LeanObject,
    mut v___y_2567_: *mut leanh::LeanObject,
    mut v___y_2568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2575_: u8 = 0;
    let mut v___x_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2579_: u8 = 0;
    let mut v_a_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2583_: u8 = 0;
    let mut v___x_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2587_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2570_ = leanh::lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_2570_, 0, v_k_2562_);
                v___x_2571_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    leanh::lean_box(0),
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
                if leanh::lean_obj_tag(v___x_2571_) == 0 {
                    v_a_2572_ = leanh::lean_ctor_get(v___x_2571_, 0);
                    v_isSharedCheck_2579_ = (!leanh::lean_is_exclusive(v___x_2571_)) as u8;
                    if v_isSharedCheck_2579_ == 0 {
                        v___x_2574_ = v___x_2571_;
                        v_isShared_2575_ = v_isSharedCheck_2579_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2572_);
                        leanh::lean_dec(v___x_2571_);
                        v___x_2574_ = leanh::lean_box(0);
                        v_isShared_2575_ = v_isSharedCheck_2579_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2580_ = leanh::lean_ctor_get(v___x_2571_, 0);
                    v_isSharedCheck_2587_ = (!leanh::lean_is_exclusive(v___x_2571_)) as u8;
                    if v_isSharedCheck_2587_ == 0 {
                        v___x_2582_ = v___x_2571_;
                        v_isShared_2583_ = v_isSharedCheck_2587_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2580_);
                        leanh::lean_dec(v___x_2571_);
                        v___x_2582_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2578_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
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
                    v_reuseFailAlloc_2586_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2580_);
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
    mut v_type_2588_: *mut leanh::LeanObject,
    mut v_maxFVars_x3f_2589_: *mut leanh::LeanObject,
    mut v_k_2590_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2591_: *mut leanh::LeanObject,
    mut v_whnfType_2592_: *mut leanh::LeanObject,
    mut v___y_2593_: *mut leanh::LeanObject,
    mut v___y_2594_: *mut leanh::LeanObject,
    mut v___y_2595_: *mut leanh::LeanObject,
    mut v___y_2596_: *mut leanh::LeanObject,
    mut v___y_2597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2598_: u8 = 0;
    let mut v_whnfType_boxed_2599_: u8 = 0;
    let mut v_res_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2598_ = (leanh::lean_unbox(v_cleanupAnnotations_2591_) as u8);
    v_whnfType_boxed_2599_ = (leanh::lean_unbox(v_whnfType_2592_) as u8);
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
    leanh::lean_dec(v___y_2596_);
    leanh::lean_dec_ref(v___y_2595_);
    leanh::lean_dec(v___y_2594_);
    leanh::lean_dec_ref(v___y_2593_);
    return v_res_2600_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5(
    mut v_00_u03b1_2601_: *mut leanh::LeanObject,
    mut v_type_2602_: *mut leanh::LeanObject,
    mut v_maxFVars_x3f_2603_: *mut leanh::LeanObject,
    mut v_k_2604_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2605_: u8,
    mut v_whnfType_2606_: u8,
    mut v___y_2607_: *mut leanh::LeanObject,
    mut v___y_2608_: *mut leanh::LeanObject,
    mut v___y_2609_: *mut leanh::LeanObject,
    mut v___y_2610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2613_: *mut leanh::LeanObject,
    mut v_type_2614_: *mut leanh::LeanObject,
    mut v_maxFVars_x3f_2615_: *mut leanh::LeanObject,
    mut v_k_2616_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_2617_: *mut leanh::LeanObject,
    mut v_whnfType_2618_: *mut leanh::LeanObject,
    mut v___y_2619_: *mut leanh::LeanObject,
    mut v___y_2620_: *mut leanh::LeanObject,
    mut v___y_2621_: *mut leanh::LeanObject,
    mut v___y_2622_: *mut leanh::LeanObject,
    mut v___y_2623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2624_: u8 = 0;
    let mut v_whnfType_boxed_2625_: u8 = 0;
    let mut v_res_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2624_ = (leanh::lean_unbox(v_cleanupAnnotations_2617_) as u8);
    v_whnfType_boxed_2625_ = (leanh::lean_unbox(v_whnfType_2618_) as u8);
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
    leanh::lean_dec(v___y_2622_);
    leanh::lean_dec_ref(v___y_2621_);
    leanh::lean_dec(v___y_2620_);
    leanh::lean_dec_ref(v___y_2619_);
    return v_res_2626_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(
    mut v_name_2627_: *mut leanh::LeanObject,
    mut v_levelParams_2628_: *mut leanh::LeanObject,
    mut v_type_2629_: *mut leanh::LeanObject,
    mut v_value_2630_: *mut leanh::LeanObject,
    mut v_hints_2631_: *mut leanh::LeanObject,
    mut v___y_2632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2636_: u8 = 0;
    let mut v___x_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2643_: u8 = 0;
    let mut v___x_2644_: u8 = 0;
    let mut v___x_2645_: u8 = 0;
    let mut v_env_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: u8 = 0;
    let mut v___x_2648_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2634_ = lean_st_ref_get(v___y_2632_);
                v_env_2646_ = leanh::lean_ctor_get(v___x_2634_, 0);
                leanh::lean_inc_ref_n(v_env_2646_, 2);
                leanh::lean_dec(v___x_2634_);
                v___x_2647_ = l_Lean_Environment_hasUnsafe(v_env_2646_, v_type_2629_);
                if v___x_2647_ == 0 {
                    v___x_2648_ = l_Lean_Environment_hasUnsafe(v_env_2646_, v_value_2630_);
                    v___y_2643_ = v___x_2648_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_env_2646_);
                    v___y_2643_ = v___x_2647_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_name_2627_);
                v___x_2637_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2637_, 0, v_name_2627_);
                leanh::lean_ctor_set(v___x_2637_, 1, v_levelParams_2628_);
                leanh::lean_ctor_set(v___x_2637_, 2, v_type_2629_);
                v___x_2638_ = leanh::lean_box(0);
                v___x_2639_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2639_, 0, v_name_2627_);
                leanh::lean_ctor_set(v___x_2639_, 1, v___x_2638_);
                v___x_2640_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                leanh::lean_ctor_set(v___x_2640_, 0, v___x_2637_);
                leanh::lean_ctor_set(v___x_2640_, 1, v_value_2630_);
                leanh::lean_ctor_set(v___x_2640_, 2, v_hints_2631_);
                leanh::lean_ctor_set(v___x_2640_, 3, v___x_2639_);
                leanh::lean_ctor_set_uint8(
                    v___x_2640_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v___y_2636_,
                );
                v___x_2641_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2641_, 0, v___x_2640_);
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
    mut v_name_2649_: *mut leanh::LeanObject,
    mut v_levelParams_2650_: *mut leanh::LeanObject,
    mut v_type_2651_: *mut leanh::LeanObject,
    mut v_value_2652_: *mut leanh::LeanObject,
    mut v_hints_2653_: *mut leanh::LeanObject,
    mut v___y_2654_: *mut leanh::LeanObject,
    mut v___y_2655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2656_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(
        v_name_2649_,
        v_levelParams_2650_,
        v_type_2651_,
        v_value_2652_,
        v_hints_2653_,
        v___y_2654_,
    );
    leanh::lean_dec(v___y_2654_);
    return v_res_2656_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8(
    mut v_name_2657_: *mut leanh::LeanObject,
    mut v_levelParams_2658_: *mut leanh::LeanObject,
    mut v_type_2659_: *mut leanh::LeanObject,
    mut v_value_2660_: *mut leanh::LeanObject,
    mut v_hints_2661_: *mut leanh::LeanObject,
    mut v___y_2662_: *mut leanh::LeanObject,
    mut v___y_2663_: *mut leanh::LeanObject,
    mut v___y_2664_: *mut leanh::LeanObject,
    mut v___y_2665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_name_2668_: *mut leanh::LeanObject,
    mut v_levelParams_2669_: *mut leanh::LeanObject,
    mut v_type_2670_: *mut leanh::LeanObject,
    mut v_value_2671_: *mut leanh::LeanObject,
    mut v_hints_2672_: *mut leanh::LeanObject,
    mut v___y_2673_: *mut leanh::LeanObject,
    mut v___y_2674_: *mut leanh::LeanObject,
    mut v___y_2675_: *mut leanh::LeanObject,
    mut v___y_2676_: *mut leanh::LeanObject,
    mut v___y_2677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_2676_);
    leanh::lean_dec_ref(v___y_2675_);
    leanh::lean_dec(v___y_2674_);
    leanh::lean_dec_ref(v___y_2673_);
    return v_res_2678_;
}
pub unsafe fn l_panic___at___00mkCtorIdx_spec__13(
    mut v_msg_2680_: *mut leanh::LeanObject,
    mut v___y_2681_: *mut leanh::LeanObject,
    mut v___y_2682_: *mut leanh::LeanObject,
    mut v___y_2683_: *mut leanh::LeanObject,
    mut v___y_2684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_26648__overap_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2686_ = l_panic___at___00mkCtorIdx_spec__13___closed__0;
    v___x_26648__overap_2687_ = lean_panic_fn_borrowed(v___f_2686_, v_msg_2680_);
    leanh::lean_inc(v___y_2684_);
    leanh::lean_inc_ref(v___y_2683_);
    leanh::lean_inc(v___y_2682_);
    leanh::lean_inc_ref(v___y_2681_);
    v___x_2688_ = leanh::lean_apply_5(
        v___x_26648__overap_2687_,
        v___y_2681_,
        v___y_2682_,
        v___y_2683_,
        v___y_2684_,
        leanh::lean_box(0),
    );
    return v___x_2688_;
}
pub unsafe fn l_panic___at___00mkCtorIdx_spec__13___boxed(
    mut v_msg_2689_: *mut leanh::LeanObject,
    mut v___y_2690_: *mut leanh::LeanObject,
    mut v___y_2691_: *mut leanh::LeanObject,
    mut v___y_2692_: *mut leanh::LeanObject,
    mut v___y_2693_: *mut leanh::LeanObject,
    mut v___y_2694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2695_ = l_panic___at___00mkCtorIdx_spec__13(
        v_msg_2689_,
        v___y_2690_,
        v___y_2691_,
        v___y_2692_,
        v___y_2693_,
    );
    leanh::lean_dec(v___y_2693_);
    leanh::lean_dec_ref(v___y_2692_);
    leanh::lean_dec(v___y_2691_);
    leanh::lean_dec_ref(v___y_2690_);
    return v_res_2695_;
}
pub unsafe fn l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0(
    mut v___y_2696_: *mut leanh::LeanObject,
    mut v_isExporting_2697_: u8,
    mut v___x_2698_: *mut leanh::LeanObject,
    mut v___y_2699_: *mut leanh::LeanObject,
    mut v___x_2700_: *mut leanh::LeanObject,
    mut v_a_x3f_2701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2714_: u8 = 0;
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2726_: u8 = 0;
    let mut v___x_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2733_: u8 = 0;
    let mut v_unused_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2736_: u8 = 0;
    let mut v_unused_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2703_ = lean_st_ref_take(v___y_2696_);
                v_env_2704_ = leanh::lean_ctor_get(v___x_2703_, 0);
                v_nextMacroScope_2705_ = leanh::lean_ctor_get(v___x_2703_, 1);
                v_ngen_2706_ = leanh::lean_ctor_get(v___x_2703_, 2);
                v_auxDeclNGen_2707_ = leanh::lean_ctor_get(v___x_2703_, 3);
                v_traceState_2708_ = leanh::lean_ctor_get(v___x_2703_, 4);
                v_messages_2709_ = leanh::lean_ctor_get(v___x_2703_, 6);
                v_infoState_2710_ = leanh::lean_ctor_get(v___x_2703_, 7);
                v_snapshotTasks_2711_ = leanh::lean_ctor_get(v___x_2703_, 8);
                v_isSharedCheck_2736_ = (!leanh::lean_is_exclusive(v___x_2703_)) as u8;
                if v_isSharedCheck_2736_ == 0 {
                    v_unused_2737_ = leanh::lean_ctor_get(v___x_2703_, 5);
                    leanh::lean_dec(v_unused_2737_);
                    v___x_2713_ = v___x_2703_;
                    v_isShared_2714_ = v_isSharedCheck_2736_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2711_);
                    leanh::lean_inc(v_infoState_2710_);
                    leanh::lean_inc(v_messages_2709_);
                    leanh::lean_inc(v_traceState_2708_);
                    leanh::lean_inc(v_auxDeclNGen_2707_);
                    leanh::lean_inc(v_ngen_2706_);
                    leanh::lean_inc(v_nextMacroScope_2705_);
                    leanh::lean_inc(v_env_2704_);
                    leanh::lean_dec(v___x_2703_);
                    v___x_2713_ = leanh::lean_box(0);
                    v_isShared_2714_ = v_isSharedCheck_2736_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2715_ = l_Lean_Environment_setExporting(v_env_2704_, v_isExporting_2697_);
                if v_isShared_2714_ == 0 {
                    leanh::lean_ctor_set(v___x_2713_, 5, v___x_2698_);
                    leanh::lean_ctor_set(v___x_2713_, 0, v___x_2715_);
                    v___x_2717_ = v___x_2713_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2735_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2715_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 1, v_nextMacroScope_2705_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 2, v_ngen_2706_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 3, v_auxDeclNGen_2707_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 4, v_traceState_2708_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 5, v___x_2698_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 6, v_messages_2709_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 7, v_infoState_2710_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 8, v_snapshotTasks_2711_);
                    v___x_2717_ = v_reuseFailAlloc_2735_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2718_ = lean_st_ref_set(v___y_2696_, v___x_2717_);
                v___x_2719_ = lean_st_ref_take(v___y_2699_);
                v_mctx_2720_ = leanh::lean_ctor_get(v___x_2719_, 0);
                v_zetaDeltaFVarIds_2721_ = leanh::lean_ctor_get(v___x_2719_, 2);
                v_postponed_2722_ = leanh::lean_ctor_get(v___x_2719_, 3);
                v_diag_2723_ = leanh::lean_ctor_get(v___x_2719_, 4);
                v_isSharedCheck_2733_ = (!leanh::lean_is_exclusive(v___x_2719_)) as u8;
                if v_isSharedCheck_2733_ == 0 {
                    v_unused_2734_ = leanh::lean_ctor_get(v___x_2719_, 1);
                    leanh::lean_dec(v_unused_2734_);
                    v___x_2725_ = v___x_2719_;
                    v_isShared_2726_ = v_isSharedCheck_2733_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_2723_);
                    leanh::lean_inc(v_postponed_2722_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_2721_);
                    leanh::lean_inc(v_mctx_2720_);
                    leanh::lean_dec(v___x_2719_);
                    v___x_2725_ = leanh::lean_box(0);
                    v_isShared_2726_ = v_isSharedCheck_2733_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2726_ == 0 {
                    leanh::lean_ctor_set(v___x_2725_, 1, v___x_2700_);
                    v___x_2728_ = v___x_2725_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2732_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_mctx_2720_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2732_, 1, v___x_2700_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2732_,
                        2,
                        v_zetaDeltaFVarIds_2721_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2732_, 3, v_postponed_2722_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2732_, 4, v_diag_2723_);
                    v___x_2728_ = v_reuseFailAlloc_2732_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2729_ = lean_st_ref_set(v___y_2699_, v___x_2728_);
                v___x_2730_ = leanh::lean_box(0);
                v___x_2731_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2731_, 0, v___x_2730_);
                return v___x_2731_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0___boxed(
    mut v___y_2738_: *mut leanh::LeanObject,
    mut v_isExporting_2739_: *mut leanh::LeanObject,
    mut v___x_2740_: *mut leanh::LeanObject,
    mut v___y_2741_: *mut leanh::LeanObject,
    mut v___x_2742_: *mut leanh::LeanObject,
    mut v_a_x3f_2743_: *mut leanh::LeanObject,
    mut v___y_2744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_2745_: u8 = 0;
    let mut v_res_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_2745_ = (leanh::lean_unbox(v_isExporting_2739_) as u8);
    v_res_2746_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0(
        v___y_2738_,
        v_isExporting_boxed_2745_,
        v___x_2740_,
        v___y_2741_,
        v___x_2742_,
        v_a_x3f_2743_,
    );
    leanh::lean_dec(v_a_x3f_2743_);
    leanh::lean_dec(v___y_2741_);
    leanh::lean_dec(v___y_2738_);
    return v_res_2746_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2747_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2747_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2748_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0_once
        ),
        _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0,
    );
    v___x_2749_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2749_, 0, v___x_2748_);
    return v___x_2749_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2750_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1_once
        ),
        _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1,
    );
    v___x_2751_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2751_, 0, v___x_2750_);
    leanh::lean_ctor_set(v___x_2751_, 1, v___x_2750_);
    return v___x_2751_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2752_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1_once
        ),
        _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1,
    );
    v___x_2753_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_2753_, 0, v___x_2752_);
    leanh::lean_ctor_set(v___x_2753_, 1, v___x_2752_);
    leanh::lean_ctor_set(v___x_2753_, 2, v___x_2752_);
    leanh::lean_ctor_set(v___x_2753_, 3, v___x_2752_);
    leanh::lean_ctor_set(v___x_2753_, 4, v___x_2752_);
    leanh::lean_ctor_set(v___x_2753_, 5, v___x_2752_);
    return v___x_2753_;
}
pub unsafe fn l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(
    mut v_x_2754_: *mut leanh::LeanObject,
    mut v_isExporting_2755_: u8,
    mut v___y_2756_: *mut leanh::LeanObject,
    mut v___y_2757_: *mut leanh::LeanObject,
    mut v___y_2758_: *mut leanh::LeanObject,
    mut v___y_2759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_2763_: u8 = 0;
    let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2775_: u8 = 0;
    let mut v___x_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2788_: u8 = 0;
    let mut v___x_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2797_: u8 = 0;
    let mut v___x_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2803_: u8 = 0;
    let mut v___x_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2807_: u8 = 0;
    let mut v_unused_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2810_: u8 = 0;
    let mut v_a_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2816_: u8 = 0;
    let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2820_: u8 = 0;
    let mut v_unused_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2823_: u8 = 0;
    let mut v_unused_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2826_: u8 = 0;
    let mut v_unused_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2761_ = lean_st_ref_get(v___y_2759_);
                v_env_2762_ = leanh::lean_ctor_get(v___x_2761_, 0);
                leanh::lean_inc_ref(v_env_2762_);
                leanh::lean_dec(v___x_2761_);
                v_isExporting_2763_ = leanh::lean_ctor_get_uint8(
                    v_env_2762_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                leanh::lean_dec_ref(v_env_2762_);
                v___x_2764_ = lean_st_ref_take(v___y_2759_);
                v_env_2765_ = leanh::lean_ctor_get(v___x_2764_, 0);
                v_nextMacroScope_2766_ = leanh::lean_ctor_get(v___x_2764_, 1);
                v_ngen_2767_ = leanh::lean_ctor_get(v___x_2764_, 2);
                v_auxDeclNGen_2768_ = leanh::lean_ctor_get(v___x_2764_, 3);
                v_traceState_2769_ = leanh::lean_ctor_get(v___x_2764_, 4);
                v_messages_2770_ = leanh::lean_ctor_get(v___x_2764_, 6);
                v_infoState_2771_ = leanh::lean_ctor_get(v___x_2764_, 7);
                v_snapshotTasks_2772_ = leanh::lean_ctor_get(v___x_2764_, 8);
                v_isSharedCheck_2826_ = (!leanh::lean_is_exclusive(v___x_2764_)) as u8;
                if v_isSharedCheck_2826_ == 0 {
                    v_unused_2827_ = leanh::lean_ctor_get(v___x_2764_, 5);
                    leanh::lean_dec(v_unused_2827_);
                    v___x_2774_ = v___x_2764_;
                    v_isShared_2775_ = v_isSharedCheck_2826_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2772_);
                    leanh::lean_inc(v_infoState_2771_);
                    leanh::lean_inc(v_messages_2770_);
                    leanh::lean_inc(v_traceState_2769_);
                    leanh::lean_inc(v_auxDeclNGen_2768_);
                    leanh::lean_inc(v_ngen_2767_);
                    leanh::lean_inc(v_nextMacroScope_2766_);
                    leanh::lean_inc(v_env_2765_);
                    leanh::lean_dec(v___x_2764_);
                    v___x_2774_ = leanh::lean_box(0);
                    v_isShared_2775_ = v_isSharedCheck_2826_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2776_ = l_Lean_Environment_setExporting(v_env_2765_, v_isExporting_2755_);
                v___x_2777_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once
                    ),
                    _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2,
                );
                if v_isShared_2775_ == 0 {
                    leanh::lean_ctor_set(v___x_2774_, 5, v___x_2777_);
                    leanh::lean_ctor_set(v___x_2774_, 0, v___x_2776_);
                    v___x_2779_ = v___x_2774_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2825_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2825_, 0, v___x_2776_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2825_, 1, v_nextMacroScope_2766_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2825_, 2, v_ngen_2767_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2825_, 3, v_auxDeclNGen_2768_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2825_, 4, v_traceState_2769_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2825_, 5, v___x_2777_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2825_, 6, v_messages_2770_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2825_, 7, v_infoState_2771_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2825_, 8, v_snapshotTasks_2772_);
                    v___x_2779_ = v_reuseFailAlloc_2825_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2780_ = lean_st_ref_set(v___y_2759_, v___x_2779_);
                v___x_2781_ = lean_st_ref_take(v___y_2757_);
                v_mctx_2782_ = leanh::lean_ctor_get(v___x_2781_, 0);
                v_zetaDeltaFVarIds_2783_ = leanh::lean_ctor_get(v___x_2781_, 2);
                v_postponed_2784_ = leanh::lean_ctor_get(v___x_2781_, 3);
                v_diag_2785_ = leanh::lean_ctor_get(v___x_2781_, 4);
                v_isSharedCheck_2823_ = (!leanh::lean_is_exclusive(v___x_2781_)) as u8;
                if v_isSharedCheck_2823_ == 0 {
                    v_unused_2824_ = leanh::lean_ctor_get(v___x_2781_, 1);
                    leanh::lean_dec(v_unused_2824_);
                    v___x_2787_ = v___x_2781_;
                    v_isShared_2788_ = v_isSharedCheck_2823_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_2785_);
                    leanh::lean_inc(v_postponed_2784_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_2783_);
                    leanh::lean_inc(v_mctx_2782_);
                    leanh::lean_dec(v___x_2781_);
                    v___x_2787_ = leanh::lean_box(0);
                    v_isShared_2788_ = v_isSharedCheck_2823_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2789_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once
                    ),
                    _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3,
                );
                if v_isShared_2788_ == 0 {
                    leanh::lean_ctor_set(v___x_2787_, 1, v___x_2789_);
                    v___x_2791_ = v___x_2787_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2822_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_mctx_2782_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 1, v___x_2789_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2822_,
                        2,
                        v_zetaDeltaFVarIds_2783_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 3, v_postponed_2784_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 4, v_diag_2785_);
                    v___x_2791_ = v_reuseFailAlloc_2822_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2792_ = lean_st_ref_set(v___y_2757_, v___x_2791_);
                leanh::lean_inc(v___y_2759_);
                leanh::lean_inc_ref(v___y_2758_);
                leanh::lean_inc(v___y_2757_);
                leanh::lean_inc_ref(v___y_2756_);
                v_r_2793_ = leanh::lean_apply_5(
                    v_x_2754_,
                    v___y_2756_,
                    v___y_2757_,
                    v___y_2758_,
                    v___y_2759_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v_r_2793_) == 0 {
                    v_a_2794_ = leanh::lean_ctor_get(v_r_2793_, 0);
                    v_isSharedCheck_2810_ = (!leanh::lean_is_exclusive(v_r_2793_)) as u8;
                    if v_isSharedCheck_2810_ == 0 {
                        v___x_2796_ = v_r_2793_;
                        v_isShared_2797_ = v_isSharedCheck_2810_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2794_);
                        leanh::lean_dec(v_r_2793_);
                        v___x_2796_ = leanh::lean_box(0);
                        v_isShared_2797_ = v_isSharedCheck_2810_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_2811_ = leanh::lean_ctor_get(v_r_2793_, 0);
                    leanh::lean_inc(v_a_2811_);
                    leanh::lean_dec_ref_known(v_r_2793_, 1);
                    v___x_2812_ = leanh::lean_box(0);
                    v___x_2813_ =
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0(
                            v___y_2759_,
                            v_isExporting_2763_,
                            v___x_2777_,
                            v___y_2757_,
                            v___x_2789_,
                            v___x_2812_,
                        );
                    v_isSharedCheck_2820_ = (!leanh::lean_is_exclusive(v___x_2813_)) as u8;
                    if v_isSharedCheck_2820_ == 0 {
                        v_unused_2821_ = leanh::lean_ctor_get(v___x_2813_, 0);
                        leanh::lean_dec(v_unused_2821_);
                        v___x_2815_ = v___x_2813_;
                        v_isShared_2816_ = v_isSharedCheck_2820_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2813_);
                        v___x_2815_ = leanh::lean_box(0);
                        v_isShared_2816_ = v_isSharedCheck_2820_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                leanh::lean_inc(v_a_2794_);
                if v_isShared_2797_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2796_, 1);
                    v___x_2799_ = v___x_2796_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2809_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_a_2794_);
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
                leanh::lean_dec_ref(v___x_2799_);
                v_isSharedCheck_2807_ = (!leanh::lean_is_exclusive(v___x_2800_)) as u8;
                if v_isSharedCheck_2807_ == 0 {
                    v_unused_2808_ = leanh::lean_ctor_get(v___x_2800_, 0);
                    leanh::lean_dec(v_unused_2808_);
                    v___x_2802_ = v___x_2800_;
                    v_isShared_2803_ = v_isSharedCheck_2807_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_dec(v___x_2800_);
                    v___x_2802_ = leanh::lean_box(0);
                    v_isShared_2803_ = v_isSharedCheck_2807_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2803_ == 0 {
                    leanh::lean_ctor_set(v___x_2802_, 0, v_a_2794_);
                    v___x_2805_ = v___x_2802_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2806_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2794_);
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
                    leanh::lean_ctor_set_tag(v___x_2815_, 1);
                    leanh::lean_ctor_set(v___x_2815_, 0, v_a_2811_);
                    v___x_2818_ = v___x_2815_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2819_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2811_);
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
    mut v_x_2828_: *mut leanh::LeanObject,
    mut v_isExporting_2829_: *mut leanh::LeanObject,
    mut v___y_2830_: *mut leanh::LeanObject,
    mut v___y_2831_: *mut leanh::LeanObject,
    mut v___y_2832_: *mut leanh::LeanObject,
    mut v___y_2833_: *mut leanh::LeanObject,
    mut v___y_2834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_2835_: u8 = 0;
    let mut v_res_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_2835_ = (leanh::lean_unbox(v_isExporting_2829_) as u8);
    v_res_2836_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(
        v_x_2828_,
        v_isExporting_boxed_2835_,
        v___y_2830_,
        v___y_2831_,
        v___y_2832_,
        v___y_2833_,
    );
    leanh::lean_dec(v___y_2833_);
    leanh::lean_dec_ref(v___y_2832_);
    leanh::lean_dec(v___y_2831_);
    leanh::lean_dec_ref(v___y_2830_);
    return v_res_2836_;
}
pub unsafe fn l_Lean_withExporting___at___00mkCtorIdx_spec__14(
    mut v_00_u03b1_2837_: *mut leanh::LeanObject,
    mut v_x_2838_: *mut leanh::LeanObject,
    mut v_isExporting_2839_: u8,
    mut v___y_2840_: *mut leanh::LeanObject,
    mut v___y_2841_: *mut leanh::LeanObject,
    mut v___y_2842_: *mut leanh::LeanObject,
    mut v___y_2843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2846_: *mut leanh::LeanObject,
    mut v_x_2847_: *mut leanh::LeanObject,
    mut v_isExporting_2848_: *mut leanh::LeanObject,
    mut v___y_2849_: *mut leanh::LeanObject,
    mut v___y_2850_: *mut leanh::LeanObject,
    mut v___y_2851_: *mut leanh::LeanObject,
    mut v___y_2852_: *mut leanh::LeanObject,
    mut v___y_2853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_2854_: u8 = 0;
    let mut v_res_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_2854_ = (leanh::lean_unbox(v_isExporting_2848_) as u8);
    v_res_2855_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14(
        v_00_u03b1_2846_,
        v_x_2847_,
        v_isExporting_boxed_2854_,
        v___y_2849_,
        v___y_2850_,
        v___y_2851_,
        v___y_2852_,
    );
    leanh::lean_dec(v___y_2852_);
    leanh::lean_dec_ref(v___y_2851_);
    leanh::lean_dec(v___y_2850_);
    leanh::lean_dec_ref(v___y_2849_);
    return v_res_2855_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5_spec__11(
    mut v_msgData_2856_: *mut leanh::LeanObject,
    mut v___y_2857_: *mut leanh::LeanObject,
    mut v___y_2858_: *mut leanh::LeanObject,
    mut v___y_2859_: *mut leanh::LeanObject,
    mut v___y_2860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2862_ = lean_st_ref_get(v___y_2860_);
    v_env_2863_ = leanh::lean_ctor_get(v___x_2862_, 0);
    leanh::lean_inc_ref(v_env_2863_);
    leanh::lean_dec(v___x_2862_);
    v___x_2864_ = lean_st_ref_get(v___y_2858_);
    v_mctx_2865_ = leanh::lean_ctor_get(v___x_2864_, 0);
    leanh::lean_inc_ref(v_mctx_2865_);
    leanh::lean_dec(v___x_2864_);
    v_lctx_2866_ = leanh::lean_ctor_get(v___y_2857_, 2);
    v_options_2867_ = leanh::lean_ctor_get(v___y_2859_, 2);
    leanh::lean_inc_ref(v_options_2867_);
    leanh::lean_inc_ref(v_lctx_2866_);
    v___x_2868_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2868_, 0, v_env_2863_);
    leanh::lean_ctor_set(v___x_2868_, 1, v_mctx_2865_);
    leanh::lean_ctor_set(v___x_2868_, 2, v_lctx_2866_);
    leanh::lean_ctor_set(v___x_2868_, 3, v_options_2867_);
    v___x_2869_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2869_, 0, v___x_2868_);
    leanh::lean_ctor_set(v___x_2869_, 1, v_msgData_2856_);
    v___x_2870_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2870_, 0, v___x_2869_);
    return v___x_2870_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5_spec__11___boxed(
    mut v_msgData_2871_: *mut leanh::LeanObject,
    mut v___y_2872_: *mut leanh::LeanObject,
    mut v___y_2873_: *mut leanh::LeanObject,
    mut v___y_2874_: *mut leanh::LeanObject,
    mut v___y_2875_: *mut leanh::LeanObject,
    mut v___y_2876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2877_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5_spec__11(v_msgData_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
    leanh::lean_dec(v___y_2875_);
    leanh::lean_dec_ref(v___y_2874_);
    leanh::lean_dec(v___y_2873_);
    leanh::lean_dec_ref(v___y_2872_);
    return v_res_2877_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(
    mut v_msg_2878_: *mut leanh::LeanObject,
    mut v___y_2879_: *mut leanh::LeanObject,
    mut v___y_2880_: *mut leanh::LeanObject,
    mut v___y_2881_: *mut leanh::LeanObject,
    mut v___y_2882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2889_: u8 = 0;
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2894_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2884_ = leanh::lean_ctor_get(v___y_2881_, 5);
                v___x_2885_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5_spec__11(v_msg_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
                v_a_2886_ = leanh::lean_ctor_get(v___x_2885_, 0);
                v_isSharedCheck_2894_ = (!leanh::lean_is_exclusive(v___x_2885_)) as u8;
                if v_isSharedCheck_2894_ == 0 {
                    v___x_2888_ = v___x_2885_;
                    v_isShared_2889_ = v_isSharedCheck_2894_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2886_);
                    leanh::lean_dec(v___x_2885_);
                    v___x_2888_ = leanh::lean_box(0);
                    v_isShared_2889_ = v_isSharedCheck_2894_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_2884_);
                v___x_2890_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2890_, 0, v_ref_2884_);
                leanh::lean_ctor_set(v___x_2890_, 1, v_a_2886_);
                if v_isShared_2889_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2888_, 1);
                    leanh::lean_ctor_set(v___x_2888_, 0, v___x_2890_);
                    v___x_2892_ = v___x_2888_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2893_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2893_, 0, v___x_2890_);
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
    mut v_msg_2895_: *mut leanh::LeanObject,
    mut v___y_2896_: *mut leanh::LeanObject,
    mut v___y_2897_: *mut leanh::LeanObject,
    mut v___y_2898_: *mut leanh::LeanObject,
    mut v___y_2899_: *mut leanh::LeanObject,
    mut v___y_2900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2901_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v_msg_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
    leanh::lean_dec(v___y_2899_);
    leanh::lean_dec_ref(v___y_2898_);
    leanh::lean_dec(v___y_2897_);
    leanh::lean_dec_ref(v___y_2896_);
    return v_res_2901_;
}
pub unsafe fn _init_l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2902_ = l_instMonadEIO(leanh::lean_box(0));
    return v___x_2902_;
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6(
    mut v_msg_2907_: *mut leanh::LeanObject,
    mut v___y_2908_: *mut leanh::LeanObject,
    mut v___y_2909_: *mut leanh::LeanObject,
    mut v___y_2910_: *mut leanh::LeanObject,
    mut v___y_2911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2918_: u8 = 0;
    let mut v_toFunctor_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2925_: u8 = 0;
    let mut v___f_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2942_: u8 = 0;
    let mut v_toFunctor_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2949_: u8 = 0;
    let mut v___f_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_30010__overap_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2968_: u8 = 0;
    let mut v_unused_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2970_: u8 = 0;
    let mut v_unused_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2974_: u8 = 0;
    let mut v_unused_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2976_: u8 = 0;
    let mut v_unused_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2913_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0_once), _init_l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0);
                v___x_2914_ = l_StateRefT_x27_instMonad___redArg(v___x_2913_);
                v_toApplicative_2915_ = leanh::lean_ctor_get(v___x_2914_, 0);
                v_isSharedCheck_2976_ = (!leanh::lean_is_exclusive(v___x_2914_)) as u8;
                if v_isSharedCheck_2976_ == 0 {
                    v_unused_2977_ = leanh::lean_ctor_get(v___x_2914_, 1);
                    leanh::lean_dec(v_unused_2977_);
                    v___x_2917_ = v___x_2914_;
                    v_isShared_2918_ = v_isSharedCheck_2976_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_2915_);
                    leanh::lean_dec(v___x_2914_);
                    v___x_2917_ = leanh::lean_box(0);
                    v_isShared_2918_ = v_isSharedCheck_2976_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2919_ = leanh::lean_ctor_get(v_toApplicative_2915_, 0);
                v_toSeq_2920_ = leanh::lean_ctor_get(v_toApplicative_2915_, 2);
                v_toSeqLeft_2921_ = leanh::lean_ctor_get(v_toApplicative_2915_, 3);
                v_toSeqRight_2922_ = leanh::lean_ctor_get(v_toApplicative_2915_, 4);
                v_isSharedCheck_2974_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_2915_)) as u8;
                if v_isSharedCheck_2974_ == 0 {
                    v_unused_2975_ = leanh::lean_ctor_get(v_toApplicative_2915_, 1);
                    leanh::lean_dec(v_unused_2975_);
                    v___x_2924_ = v_toApplicative_2915_;
                    v_isShared_2925_ = v_isSharedCheck_2974_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_2922_);
                    leanh::lean_inc(v_toSeqLeft_2921_);
                    leanh::lean_inc(v_toSeq_2920_);
                    leanh::lean_inc(v_toFunctor_2919_);
                    leanh::lean_dec(v_toApplicative_2915_);
                    v___x_2924_ = leanh::lean_box(0);
                    v_isShared_2925_ = v_isSharedCheck_2974_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2926_ = l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__1;
                v___f_2927_ = l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__2;
                leanh::lean_inc_ref(v_toFunctor_2919_);
                v___f_2928_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2928_, 0, v_toFunctor_2919_);
                v___f_2929_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2929_, 0, v_toFunctor_2919_);
                v___x_2930_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2930_, 0, v___f_2928_);
                leanh::lean_ctor_set(v___x_2930_, 1, v___f_2929_);
                v___f_2931_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2931_, 0, v_toSeqRight_2922_);
                v___f_2932_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2932_, 0, v_toSeqLeft_2921_);
                v___f_2933_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2933_, 0, v_toSeq_2920_);
                if v_isShared_2925_ == 0 {
                    leanh::lean_ctor_set(v___x_2924_, 4, v___f_2931_);
                    leanh::lean_ctor_set(v___x_2924_, 3, v___f_2932_);
                    leanh::lean_ctor_set(v___x_2924_, 2, v___f_2933_);
                    leanh::lean_ctor_set(v___x_2924_, 1, v___f_2926_);
                    leanh::lean_ctor_set(v___x_2924_, 0, v___x_2930_);
                    v___x_2935_ = v___x_2924_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2973_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2930_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 1, v___f_2926_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 2, v___f_2933_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 3, v___f_2932_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 4, v___f_2931_);
                    v___x_2935_ = v_reuseFailAlloc_2973_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2918_ == 0 {
                    leanh::lean_ctor_set(v___x_2917_, 1, v___f_2927_);
                    leanh::lean_ctor_set(v___x_2917_, 0, v___x_2935_);
                    v___x_2937_ = v___x_2917_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2972_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2972_, 0, v___x_2935_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2972_, 1, v___f_2927_);
                    v___x_2937_ = v_reuseFailAlloc_2972_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2938_ = l_StateRefT_x27_instMonad___redArg(v___x_2937_);
                v_toApplicative_2939_ = leanh::lean_ctor_get(v___x_2938_, 0);
                v_isSharedCheck_2970_ = (!leanh::lean_is_exclusive(v___x_2938_)) as u8;
                if v_isSharedCheck_2970_ == 0 {
                    v_unused_2971_ = leanh::lean_ctor_get(v___x_2938_, 1);
                    leanh::lean_dec(v_unused_2971_);
                    v___x_2941_ = v___x_2938_;
                    v_isShared_2942_ = v_isSharedCheck_2970_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_toApplicative_2939_);
                    leanh::lean_dec(v___x_2938_);
                    v___x_2941_ = leanh::lean_box(0);
                    v_isShared_2942_ = v_isSharedCheck_2970_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_2943_ = leanh::lean_ctor_get(v_toApplicative_2939_, 0);
                v_toSeq_2944_ = leanh::lean_ctor_get(v_toApplicative_2939_, 2);
                v_toSeqLeft_2945_ = leanh::lean_ctor_get(v_toApplicative_2939_, 3);
                v_toSeqRight_2946_ = leanh::lean_ctor_get(v_toApplicative_2939_, 4);
                v_isSharedCheck_2968_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_2939_)) as u8;
                if v_isSharedCheck_2968_ == 0 {
                    v_unused_2969_ = leanh::lean_ctor_get(v_toApplicative_2939_, 1);
                    leanh::lean_dec(v_unused_2969_);
                    v___x_2948_ = v_toApplicative_2939_;
                    v_isShared_2949_ = v_isSharedCheck_2968_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_2946_);
                    leanh::lean_inc(v_toSeqLeft_2945_);
                    leanh::lean_inc(v_toSeq_2944_);
                    leanh::lean_inc(v_toFunctor_2943_);
                    leanh::lean_dec(v_toApplicative_2939_);
                    v___x_2948_ = leanh::lean_box(0);
                    v_isShared_2949_ = v_isSharedCheck_2968_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_2950_ = l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__3;
                v___f_2951_ = l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__4;
                leanh::lean_inc_ref(v_toFunctor_2943_);
                v___f_2952_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2952_, 0, v_toFunctor_2943_);
                v___f_2953_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2953_, 0, v_toFunctor_2943_);
                v___x_2954_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2954_, 0, v___f_2952_);
                leanh::lean_ctor_set(v___x_2954_, 1, v___f_2953_);
                v___f_2955_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2955_, 0, v_toSeqRight_2946_);
                v___f_2956_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2956_, 0, v_toSeqLeft_2945_);
                v___f_2957_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_2957_, 0, v_toSeq_2944_);
                if v_isShared_2949_ == 0 {
                    leanh::lean_ctor_set(v___x_2948_, 4, v___f_2955_);
                    leanh::lean_ctor_set(v___x_2948_, 3, v___f_2956_);
                    leanh::lean_ctor_set(v___x_2948_, 2, v___f_2957_);
                    leanh::lean_ctor_set(v___x_2948_, 1, v___f_2950_);
                    leanh::lean_ctor_set(v___x_2948_, 0, v___x_2954_);
                    v___x_2959_ = v___x_2948_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2967_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2954_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2967_, 1, v___f_2950_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2967_, 2, v___f_2957_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2967_, 3, v___f_2956_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2967_, 4, v___f_2955_);
                    v___x_2959_ = v_reuseFailAlloc_2967_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2942_ == 0 {
                    leanh::lean_ctor_set(v___x_2941_, 1, v___f_2951_);
                    leanh::lean_ctor_set(v___x_2941_, 0, v___x_2959_);
                    v___x_2961_ = v___x_2941_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2966_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2966_, 0, v___x_2959_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2966_, 1, v___f_2951_);
                    v___x_2961_ = v_reuseFailAlloc_2966_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2962_ = leanh::lean_box(0);
                v___x_2963_ = l_instInhabitedOfMonad___redArg(v___x_2961_, v___x_2962_);
                v___x_30010__overap_2964_ = lean_panic_fn_borrowed(v___x_2963_, v_msg_2907_);
                leanh::lean_dec(v___x_2963_);
                leanh::lean_inc(v___y_2911_);
                leanh::lean_inc_ref(v___y_2910_);
                leanh::lean_inc(v___y_2909_);
                leanh::lean_inc_ref(v___y_2908_);
                v___x_2965_ = leanh::lean_apply_5(
                    v___x_30010__overap_2964_,
                    v___y_2908_,
                    v___y_2909_,
                    v___y_2910_,
                    v___y_2911_,
                    leanh::lean_box(0),
                );
                return v___x_2965_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___boxed(
    mut v_msg_2978_: *mut leanh::LeanObject,
    mut v___y_2979_: *mut leanh::LeanObject,
    mut v___y_2980_: *mut leanh::LeanObject,
    mut v___y_2981_: *mut leanh::LeanObject,
    mut v___y_2982_: *mut leanh::LeanObject,
    mut v___y_2983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2984_ = l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6(
        v_msg_2978_,
        v___y_2979_,
        v___y_2980_,
        v___y_2981_,
        v___y_2982_,
    );
    leanh::lean_dec(v___y_2982_);
    leanh::lean_dec_ref(v___y_2981_);
    leanh::lean_dec(v___y_2980_);
    leanh::lean_dec_ref(v___y_2979_);
    return v_res_2984_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2986_ = l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__0;
    v___x_2987_ = l_Lean_stringToMessageData(v___x_2986_);
    return v___x_2987_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2989_ = l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__2;
    v___x_2990_ = l_Lean_stringToMessageData(v___x_2989_);
    return v___x_2990_;
}
pub unsafe fn _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2994_ = l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__6;
    v___x_2995_ = leanh::lean_unsigned_to_nat(11);
    v___x_2996_ = leanh::lean_unsigned_to_nat(122);
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
    mut v_constName_3000_: *mut leanh::LeanObject,
    mut v___y_3001_: *mut leanh::LeanObject,
    mut v___y_3002_: *mut leanh::LeanObject,
    mut v___y_3003_: *mut leanh::LeanObject,
    mut v___y_3004_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: u8 = 0;
    let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: u8 = 0;
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3019_: u8 = 0;
    let mut v___x_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3024_: u8 = 0;
    let mut v___x_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3028_: u8 = 0;
    let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3034_: u8 = 0;
    let mut v_val_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3039_: u8 = 0;
    let mut v_a_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3043_: u8 = 0;
    let mut v___x_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3047_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3014_ = lean_st_ref_get(v___y_3004_);
                v_env_3015_ = leanh::lean_ctor_get(v___x_3014_, 0);
                leanh::lean_inc_ref(v_env_3015_);
                leanh::lean_dec(v___x_3014_);
                v___x_3016_ = 0;
                leanh::lean_inc(v_constName_3000_);
                v___x_3017_ =
                    l_Lean_Environment_findAsync_x3f(v_env_3015_, v_constName_3000_, v___x_3016_);
                if leanh::lean_obj_tag(v___x_3017_) == 1 {
                    v_val_3018_ = leanh::lean_ctor_get(v___x_3017_, 0);
                    leanh::lean_inc(v_val_3018_);
                    leanh::lean_dec_ref_known(v___x_3017_, 1);
                    v_kind_3019_ = leanh::lean_ctor_get_uint8(
                        v_val_3018_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    if v_kind_3019_ == 6 {
                        v___x_3020_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_3018_);
                        if leanh::lean_obj_tag(v___x_3020_) == 6 {
                            leanh::lean_dec(v_constName_3000_);
                            v_val_3021_ = leanh::lean_ctor_get(v___x_3020_, 0);
                            v_isSharedCheck_3028_ =
                                (!leanh::lean_is_exclusive(v___x_3020_)) as u8;
                            if v_isSharedCheck_3028_ == 0 {
                                v___x_3023_ = v___x_3020_;
                                v_isShared_3024_ = v_isSharedCheck_3028_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_3021_);
                                leanh::lean_dec(v___x_3020_);
                                v___x_3023_ = leanh::lean_box(0);
                                v_isShared_3024_ = v_isSharedCheck_3028_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_3020_);
                            v___x_3029_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7), core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7_once), _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7);
                            v___x_3030_ = l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6(v___x_3029_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
                            if leanh::lean_obj_tag(v___x_3030_) == 0 {
                                v_a_3031_ = leanh::lean_ctor_get(v___x_3030_, 0);
                                v_isSharedCheck_3039_ =
                                    (!leanh::lean_is_exclusive(v___x_3030_)) as u8;
                                if v_isSharedCheck_3039_ == 0 {
                                    v___x_3033_ = v___x_3030_;
                                    v_isShared_3034_ = v_isSharedCheck_3039_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3031_);
                                    leanh::lean_dec(v___x_3030_);
                                    v___x_3033_ = leanh::lean_box(0);
                                    v_isShared_3034_ = v_isSharedCheck_3039_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_constName_3000_);
                                v_a_3040_ = leanh::lean_ctor_get(v___x_3030_, 0);
                                v_isSharedCheck_3047_ =
                                    (!leanh::lean_is_exclusive(v___x_3030_)) as u8;
                                if v_isSharedCheck_3047_ == 0 {
                                    v___x_3042_ = v___x_3030_;
                                    v_isShared_3043_ = v_isSharedCheck_3047_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3040_);
                                    leanh::lean_dec(v___x_3030_);
                                    v___x_3042_ = leanh::lean_box(0);
                                    v_isShared_3043_ = v_isSharedCheck_3047_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_val_3018_);
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3017_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3007_ = leanh::lean_obj_once(
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
                v___x_3010_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3010_, 0, v___x_3007_);
                leanh::lean_ctor_set(v___x_3010_, 1, v___x_3009_);
                v___x_3011_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3_once
                    ),
                    _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3,
                );
                v___x_3012_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3012_, 0, v___x_3010_);
                leanh::lean_ctor_set(v___x_3012_, 1, v___x_3011_);
                v___x_3013_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v___x_3012_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
                return v___x_3013_;
            }
            2 => {
                if v_isShared_3024_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3023_, 0);
                    v___x_3026_ = v___x_3023_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3027_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_val_3021_);
                    v___x_3026_ = v_reuseFailAlloc_3027_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3026_;
            }
            4 => {
                if leanh::lean_obj_tag(v_a_3031_) == 0 {
                    leanh::lean_del_object(v___x_3033_);
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_constName_3000_);
                    v_val_3035_ = leanh::lean_ctor_get(v_a_3031_, 0);
                    leanh::lean_inc(v_val_3035_);
                    leanh::lean_dec_ref_known(v_a_3031_, 1);
                    if v_isShared_3034_ == 0 {
                        leanh::lean_ctor_set(v___x_3033_, 0, v_val_3035_);
                        v___x_3037_ = v___x_3033_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3038_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_val_3035_);
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
                    v_reuseFailAlloc_3046_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_a_3040_);
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
    mut v_constName_3048_: *mut leanh::LeanObject,
    mut v___y_3049_: *mut leanh::LeanObject,
    mut v___y_3050_: *mut leanh::LeanObject,
    mut v___y_3051_: *mut leanh::LeanObject,
    mut v___y_3052_: *mut leanh::LeanObject,
    mut v___y_3053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3054_ = l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4(
        v_constName_3048_,
        v___y_3049_,
        v___y_3050_,
        v___y_3051_,
        v___y_3052_,
    );
    leanh::lean_dec(v___y_3052_);
    leanh::lean_dec_ref(v___y_3051_);
    leanh::lean_dec(v___y_3050_);
    leanh::lean_dec_ref(v___y_3049_);
    return v_res_3054_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___lam__0(
    mut v_cidx_3055_: *mut leanh::LeanObject,
    mut v___x_3056_: u8,
    mut v___x_3057_: u8,
    mut v___x_3058_: u8,
    mut v_ys_3059_: *mut leanh::LeanObject,
    mut v_x_3060_: *mut leanh::LeanObject,
    mut v___y_3061_: *mut leanh::LeanObject,
    mut v___y_3062_: *mut leanh::LeanObject,
    mut v___y_3063_: *mut leanh::LeanObject,
    mut v___y_3064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_cidx_3068_: *mut leanh::LeanObject,
    mut v___x_3069_: *mut leanh::LeanObject,
    mut v___x_3070_: *mut leanh::LeanObject,
    mut v___x_3071_: *mut leanh::LeanObject,
    mut v_ys_3072_: *mut leanh::LeanObject,
    mut v_x_3073_: *mut leanh::LeanObject,
    mut v___y_3074_: *mut leanh::LeanObject,
    mut v___y_3075_: *mut leanh::LeanObject,
    mut v___y_3076_: *mut leanh::LeanObject,
    mut v___y_3077_: *mut leanh::LeanObject,
    mut v___y_3078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_34834__boxed_3079_: u8 = 0;
    let mut v___x_34835__boxed_3080_: u8 = 0;
    let mut v___x_34836__boxed_3081_: u8 = 0;
    let mut v_res_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_34834__boxed_3079_ = (leanh::lean_unbox(v___x_3069_) as u8);
    v___x_34835__boxed_3080_ = (leanh::lean_unbox(v___x_3070_) as u8);
    v___x_34836__boxed_3081_ = (leanh::lean_unbox(v___x_3071_) as u8);
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
    leanh::lean_dec(v___y_3077_);
    leanh::lean_dec_ref(v___y_3076_);
    leanh::lean_dec(v___y_3075_);
    leanh::lean_dec_ref(v___y_3074_);
    leanh::lean_dec_ref(v_x_3073_);
    leanh::lean_dec_ref(v_ys_3072_);
    return v_res_3082_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg(
    mut v___x_3083_: u8,
    mut v___x_3084_: *mut leanh::LeanObject,
    mut v_as_x27_3085_: *mut leanh::LeanObject,
    mut v_b_3086_: *mut leanh::LeanObject,
    mut v___y_3087_: *mut leanh::LeanObject,
    mut v___y_3088_: *mut leanh::LeanObject,
    mut v___y_3089_: *mut leanh::LeanObject,
    mut v___y_3090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cidx_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3105_: u8 = 0;
    let mut v___x_3106_: u8 = 0;
    let mut v___x_3107_: u8 = 0;
    let mut v___x_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3119_: u8 = 0;
    let mut v_a_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3123_: u8 = 0;
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3127_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_3085_) == 0 {
                    v___x_3092_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3092_, 0, v_b_3086_);
                    return v___x_3092_;
                } else {
                    v_head_3093_ = leanh::lean_ctor_get(v_as_x27_3085_, 0);
                    v_tail_3094_ = leanh::lean_ctor_get(v_as_x27_3085_, 1);
                    leanh::lean_inc(v_head_3093_);
                    v___x_3095_ = l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4(
                        v_head_3093_,
                        v___y_3087_,
                        v___y_3088_,
                        v___y_3089_,
                        v___y_3090_,
                    );
                    if leanh::lean_obj_tag(v___x_3095_) == 0 {
                        v_a_3096_ = leanh::lean_ctor_get(v___x_3095_, 0);
                        leanh::lean_inc(v_a_3096_);
                        leanh::lean_dec_ref_known(v___x_3095_, 1);
                        v_toConstantVal_3097_ = leanh::lean_ctor_get(v_a_3096_, 0);
                        leanh::lean_inc_ref(v_toConstantVal_3097_);
                        v_cidx_3098_ = leanh::lean_ctor_get(v_a_3096_, 2);
                        leanh::lean_inc(v_cidx_3098_);
                        v_numFields_3099_ = leanh::lean_ctor_get(v_a_3096_, 4);
                        leanh::lean_inc(v_numFields_3099_);
                        leanh::lean_dec(v_a_3096_);
                        v_type_3100_ = leanh::lean_ctor_get(v_toConstantVal_3097_, 2);
                        leanh::lean_inc_ref(v_type_3100_);
                        leanh::lean_dec_ref(v_toConstantVal_3097_);
                        v___x_3101_ = l_Lean_Meta_instantiateForall(
                            v_type_3100_,
                            v___x_3084_,
                            v___y_3087_,
                            v___y_3088_,
                            v___y_3089_,
                            v___y_3090_,
                        );
                        if leanh::lean_obj_tag(v___x_3101_) == 0 {
                            v_a_3102_ = leanh::lean_ctor_get(v___x_3101_, 0);
                            v_isSharedCheck_3119_ =
                                (!leanh::lean_is_exclusive(v___x_3101_)) as u8;
                            if v_isSharedCheck_3119_ == 0 {
                                v___x_3104_ = v___x_3101_;
                                v_isShared_3105_ = v_isSharedCheck_3119_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3102_);
                                leanh::lean_dec(v___x_3101_);
                                v___x_3104_ = leanh::lean_box(0);
                                v_isShared_3105_ = v_isSharedCheck_3119_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_numFields_3099_);
                            leanh::lean_dec(v_cidx_3098_);
                            leanh::lean_dec_ref(v_b_3086_);
                            return v___x_3101_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_3086_);
                        v_a_3120_ = leanh::lean_ctor_get(v___x_3095_, 0);
                        v_isSharedCheck_3127_ =
                            (!leanh::lean_is_exclusive(v___x_3095_)) as u8;
                        if v_isSharedCheck_3127_ == 0 {
                            v___x_3122_ = v___x_3095_;
                            v_isShared_3123_ = v_isSharedCheck_3127_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3120_);
                            leanh::lean_dec(v___x_3095_);
                            v___x_3122_ = leanh::lean_box(0);
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
                v___x_3108_ = leanh::lean_box((v___x_3106_) as usize);
                v___x_3109_ = leanh::lean_box((v___x_3083_) as usize);
                v___x_3110_ = leanh::lean_box((v___x_3107_) as usize);
                v___f_3111_ = leanh::lean_alloc_closure(
                    l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    11,
                    4,
                );
                leanh::lean_closure_set(v___f_3111_, 0, v_cidx_3098_);
                leanh::lean_closure_set(v___f_3111_, 1, v___x_3108_);
                leanh::lean_closure_set(v___f_3111_, 2, v___x_3109_);
                leanh::lean_closure_set(v___f_3111_, 3, v___x_3110_);
                if v_isShared_3105_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3104_, 1);
                    leanh::lean_ctor_set(v___x_3104_, 0, v_numFields_3099_);
                    v___x_3113_ = v___x_3104_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3118_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_numFields_3099_);
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
                if leanh::lean_obj_tag(v___x_3114_) == 0 {
                    v_a_3115_ = leanh::lean_ctor_get(v___x_3114_, 0);
                    leanh::lean_inc(v_a_3115_);
                    leanh::lean_dec_ref_known(v___x_3114_, 1);
                    v___x_3116_ = l_Lean_Expr_app___override(v_b_3086_, v_a_3115_);
                    v_as_x27_3085_ = v_tail_3094_;
                    v_b_3086_ = v___x_3116_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_b_3086_);
                    return v___x_3114_;
                }
            }
            3 => {
                if v_isShared_3123_ == 0 {
                    v___x_3125_ = v___x_3122_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3126_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3120_);
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
    mut v___x_3128_: *mut leanh::LeanObject,
    mut v___x_3129_: *mut leanh::LeanObject,
    mut v_as_x27_3130_: *mut leanh::LeanObject,
    mut v_b_3131_: *mut leanh::LeanObject,
    mut v___y_3132_: *mut leanh::LeanObject,
    mut v___y_3133_: *mut leanh::LeanObject,
    mut v___y_3134_: *mut leanh::LeanObject,
    mut v___y_3135_: *mut leanh::LeanObject,
    mut v___y_3136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_34865__boxed_3137_: u8 = 0;
    let mut v_res_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_34865__boxed_3137_ = (leanh::lean_unbox(v___x_3128_) as u8);
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
    leanh::lean_dec(v___y_3135_);
    leanh::lean_dec_ref(v___y_3134_);
    leanh::lean_dec(v___y_3133_);
    leanh::lean_dec_ref(v___y_3132_);
    leanh::lean_dec(v_as_x27_3130_);
    leanh::lean_dec_ref(v___x_3129_);
    return v_res_3138_;
}
pub unsafe fn _init_l_mkCtorIdx___lam__0___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3139_ = leanh::lean_box(0);
    v___x_3140_ = l_Lean_Level_succ___override(v___x_3139_);
    return v___x_3140_;
}
pub unsafe fn l_mkCtorIdx___lam__0(
    mut v_xs_3141_: *mut leanh::LeanObject,
    mut v___x_3142_: u8,
    mut v___x_3143_: u8,
    mut v___x_3144_: u8,
    mut v_val_3145_: *mut leanh::LeanObject,
    mut v___x_3146_: *mut leanh::LeanObject,
    mut v___x_3147_: *mut leanh::LeanObject,
    mut v___x_3148_: *mut leanh::LeanObject,
    mut v___x_3149_: *mut leanh::LeanObject,
    mut v___x_3150_: *mut leanh::LeanObject,
    mut v_ctors_3151_: *mut leanh::LeanObject,
    mut v___x_3152_: *mut leanh::LeanObject,
    mut v_x_3153_: *mut leanh::LeanObject,
    mut v___y_3154_: *mut leanh::LeanObject,
    mut v___y_3155_: *mut leanh::LeanObject,
    mut v___y_3156_: *mut leanh::LeanObject,
    mut v___y_3157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_value_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: u8 = 0;
    let mut v___x_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3163_ = l_Lean_InductiveVal_numCtors(v_val_3145_);
                v___x_3164_ = leanh::lean_unsigned_to_nat(1);
                v___x_3165_ = lean_nat_dec_eq(v___x_3163_, v___x_3164_);
                leanh::lean_dec(v___x_3163_);
                if v___x_3165_ == 0 {
                    leanh::lean_dec(v___x_3152_);
                    leanh::lean_inc_ref(v_x_3153_);
                    leanh::lean_inc_ref(v___x_3146_);
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
                    leanh::lean_dec_ref(v___x_3166_);
                    if leanh::lean_obj_tag(v___x_3167_) == 0 {
                        v_a_3168_ = leanh::lean_ctor_get(v___x_3167_, 0);
                        leanh::lean_inc(v_a_3168_);
                        leanh::lean_dec_ref_known(v___x_3167_, 1);
                        v___x_3169_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_mkCtorIdx___lam__0___closed__0),
                            core::ptr::addr_of_mut!(l_mkCtorIdx___lam__0___closed__0_once),
                            _init_l_mkCtorIdx___lam__0___closed__0,
                        );
                        v___x_3170_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3170_, 0, v___x_3169_);
                        leanh::lean_ctor_set(v___x_3170_, 1, v___x_3148_);
                        v___x_3171_ = l_Lean_mkConst(v___x_3149_, v___x_3170_);
                        v___x_3172_ = l_Lean_mkAppN(v___x_3171_, v___x_3150_);
                        v___x_3173_ = l_Lean_Expr_app___override(v___x_3172_, v_a_3168_);
                        v___x_3174_ = l_Lean_mkAppN(v___x_3173_, v___x_3146_);
                        leanh::lean_dec_ref(v___x_3146_);
                        leanh::lean_inc_ref(v_x_3153_);
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
                        if leanh::lean_obj_tag(v___x_3176_) == 0 {
                            v_a_3177_ = leanh::lean_ctor_get(v___x_3176_, 0);
                            leanh::lean_inc(v_a_3177_);
                            leanh::lean_dec_ref_known(v___x_3176_, 1);
                            v_value_3160_ = v_a_3177_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_x_3153_);
                            leanh::lean_dec_ref(v_xs_3141_);
                            return v___x_3176_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_x_3153_);
                        leanh::lean_dec(v___x_3149_);
                        leanh::lean_dec(v___x_3148_);
                        leanh::lean_dec_ref(v___x_3146_);
                        leanh::lean_dec_ref(v_xs_3141_);
                        return v___x_3167_;
                    }
                } else {
                    leanh::lean_dec(v___x_3149_);
                    leanh::lean_dec(v___x_3148_);
                    leanh::lean_dec_ref(v___x_3147_);
                    leanh::lean_dec_ref(v___x_3146_);
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
                leanh::lean_dec_ref(v___x_3161_);
                return v___x_3162_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_mkCtorIdx___lam__0___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_xs_3179_: *mut leanh::LeanObject = *_args.add(0);
    let mut v___x_3180_: *mut leanh::LeanObject = *_args.add(1);
    let mut v___x_3181_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___x_3182_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_val_3183_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___x_3184_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___x_3185_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_3186_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___x_3187_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___x_3188_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_ctors_3189_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___x_3190_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_x_3191_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_3192_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_3193_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_3194_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_3195_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_3196_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___x_34956__boxed_3197_: u8 = 0;
    let mut v___x_34957__boxed_3198_: u8 = 0;
    let mut v___x_34958__boxed_3199_: u8 = 0;
    let mut v_res_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_34956__boxed_3197_ = (leanh::lean_unbox(v___x_3180_) as u8);
    v___x_34957__boxed_3198_ = (leanh::lean_unbox(v___x_3181_) as u8);
    v___x_34958__boxed_3199_ = (leanh::lean_unbox(v___x_3182_) as u8);
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
    leanh::lean_dec(v___y_3195_);
    leanh::lean_dec_ref(v___y_3194_);
    leanh::lean_dec(v___y_3193_);
    leanh::lean_dec_ref(v___y_3192_);
    leanh::lean_dec(v_ctors_3189_);
    leanh::lean_dec_ref(v___x_3188_);
    leanh::lean_dec_ref(v_val_3183_);
    return v_res_3200_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3201_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3201_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3202_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0);
    v___x_3203_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3203_, 0, v___x_3202_);
    return v___x_3203_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3204_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1);
    v___x_3205_ = leanh::lean_unsigned_to_nat(0);
    v___x_3206_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_3206_, 0, v___x_3205_);
    leanh::lean_ctor_set(v___x_3206_, 1, v___x_3205_);
    leanh::lean_ctor_set(v___x_3206_, 2, v___x_3205_);
    leanh::lean_ctor_set(v___x_3206_, 3, v___x_3205_);
    leanh::lean_ctor_set(v___x_3206_, 4, v___x_3204_);
    leanh::lean_ctor_set(v___x_3206_, 5, v___x_3204_);
    leanh::lean_ctor_set(v___x_3206_, 6, v___x_3204_);
    leanh::lean_ctor_set(v___x_3206_, 7, v___x_3204_);
    leanh::lean_ctor_set(v___x_3206_, 8, v___x_3204_);
    leanh::lean_ctor_set(v___x_3206_, 9, v___x_3204_);
    return v___x_3206_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3207_ = leanh::lean_unsigned_to_nat(32);
    v___x_3208_ = lean_mk_empty_array_with_capacity(v___x_3207_);
    v___x_3209_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3209_, 0, v___x_3208_);
    return v___x_3209_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3210_: usize = 0;
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3210_ = 5usize;
    v___x_3211_ = leanh::lean_unsigned_to_nat(0);
    v___x_3212_ = leanh::lean_unsigned_to_nat(32);
    v___x_3213_ = lean_mk_empty_array_with_capacity(v___x_3212_);
    v___x_3214_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3);
    v___x_3215_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_3215_, 0, v___x_3214_);
    leanh::lean_ctor_set(v___x_3215_, 1, v___x_3213_);
    leanh::lean_ctor_set(v___x_3215_, 2, v___x_3211_);
    leanh::lean_ctor_set(v___x_3215_, 3, v___x_3211_);
    leanh::lean_ctor_set_usize(v___x_3215_, 4, v___x_3210_);
    return v___x_3215_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3216_ = leanh::lean_box(1);
    v___x_3217_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4);
    v___x_3218_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1);
    v___x_3219_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3219_, 0, v___x_3218_);
    leanh::lean_ctor_set(v___x_3219_, 1, v___x_3217_);
    leanh::lean_ctor_set(v___x_3219_, 2, v___x_3216_);
    return v___x_3219_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3221_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__6;
    v___x_3222_ = l_Lean_stringToMessageData(v___x_3221_);
    return v___x_3222_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3224_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__8;
    v___x_3225_ = l_Lean_stringToMessageData(v___x_3224_);
    return v___x_3225_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3227_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__10;
    v___x_3228_ = l_Lean_stringToMessageData(v___x_3227_);
    return v___x_3228_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3230_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__12;
    v___x_3231_ = l_Lean_stringToMessageData(v___x_3230_);
    return v___x_3231_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3233_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__14;
    v___x_3234_ = l_Lean_stringToMessageData(v___x_3233_);
    return v___x_3234_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3236_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__16;
    v___x_3237_ = l_Lean_stringToMessageData(v___x_3236_);
    return v___x_3237_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3239_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__18;
    v___x_3240_ = l_Lean_stringToMessageData(v___x_3239_);
    return v___x_3240_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(
    mut v_msg_3241_: *mut leanh::LeanObject,
    mut v_declHint_3242_: *mut leanh::LeanObject,
    mut v___y_3243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: u8 = 0;
    let mut v_isExporting_3248_: u8 = 0;
    let mut v___x_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: u8 = 0;
    let mut v___x_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3270_: u8 = 0;
    let mut v___x_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: u8 = 0;
    let mut v___x_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3302_: u8 = 0;
    let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3245_ = lean_st_ref_get(v___y_3243_);
                v_env_3246_ = leanh::lean_ctor_get(v___x_3245_, 0);
                leanh::lean_inc_ref(v_env_3246_);
                leanh::lean_dec(v___x_3245_);
                v___x_3247_ = l_Lean_Name_isAnonymous(v_declHint_3242_);
                if v___x_3247_ == 0 {
                    v_isExporting_3248_ = leanh::lean_ctor_get_uint8(
                        v_env_3246_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_3248_ == 0 {
                        leanh::lean_dec_ref(v_env_3246_);
                        leanh::lean_dec(v_declHint_3242_);
                        v___x_3249_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3249_, 0, v_msg_3241_);
                        return v___x_3249_;
                    } else {
                        leanh::lean_inc_ref(v_env_3246_);
                        v___x_3250_ = l_Lean_Environment_setExporting(v_env_3246_, v___x_3247_);
                        leanh::lean_inc(v_declHint_3242_);
                        leanh::lean_inc_ref(v___x_3250_);
                        v___x_3251_ = l_Lean_Environment_contains(
                            v___x_3250_,
                            v_declHint_3242_,
                            v_isExporting_3248_,
                        );
                        if v___x_3251_ == 0 {
                            leanh::lean_dec_ref(v___x_3250_);
                            leanh::lean_dec_ref(v_env_3246_);
                            leanh::lean_dec(v_declHint_3242_);
                            v___x_3252_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3252_, 0, v_msg_3241_);
                            return v___x_3252_;
                        } else {
                            v___x_3253_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2);
                            v___x_3254_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5);
                            v___x_3255_ = l_Lean_Options_empty;
                            v___x_3256_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_3256_, 0, v___x_3250_);
                            leanh::lean_ctor_set(v___x_3256_, 1, v___x_3253_);
                            leanh::lean_ctor_set(v___x_3256_, 2, v___x_3254_);
                            leanh::lean_ctor_set(v___x_3256_, 3, v___x_3255_);
                            leanh::lean_inc(v_declHint_3242_);
                            v___x_3257_ =
                                l_Lean_MessageData_ofConstName(v_declHint_3242_, v___x_3247_);
                            v_c_3258_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_3258_, 0, v___x_3256_);
                            leanh::lean_ctor_set(v_c_3258_, 1, v___x_3257_);
                            v___x_3259_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_3246_,
                                v_declHint_3242_,
                            );
                            if leanh::lean_obj_tag(v___x_3259_) == 0 {
                                leanh::lean_dec_ref(v_env_3246_);
                                leanh::lean_dec(v_declHint_3242_);
                                v___x_3260_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7);
                                v___x_3261_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3261_, 0, v___x_3260_);
                                leanh::lean_ctor_set(v___x_3261_, 1, v_c_3258_);
                                v___x_3262_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9);
                                v___x_3263_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3263_, 0, v___x_3261_);
                                leanh::lean_ctor_set(v___x_3263_, 1, v___x_3262_);
                                v___x_3264_ = l_Lean_MessageData_note(v___x_3263_);
                                v___x_3265_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3265_, 0, v_msg_3241_);
                                leanh::lean_ctor_set(v___x_3265_, 1, v___x_3264_);
                                v___x_3266_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3266_, 0, v___x_3265_);
                                return v___x_3266_;
                            } else {
                                v_val_3267_ = leanh::lean_ctor_get(v___x_3259_, 0);
                                v_isSharedCheck_3302_ =
                                    (!leanh::lean_is_exclusive(v___x_3259_)) as u8;
                                if v_isSharedCheck_3302_ == 0 {
                                    v___x_3269_ = v___x_3259_;
                                    v_isShared_3270_ = v_isSharedCheck_3302_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_3267_);
                                    leanh::lean_dec(v___x_3259_);
                                    v___x_3269_ = leanh::lean_box(0);
                                    v_isShared_3270_ = v_isSharedCheck_3302_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_3246_);
                    leanh::lean_dec(v_declHint_3242_);
                    v___x_3303_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3303_, 0, v_msg_3241_);
                    return v___x_3303_;
                }
            }
            1 => {
                v___x_3271_ = leanh::lean_box(0);
                v___x_3272_ = l_Lean_Environment_header(v_env_3246_);
                leanh::lean_dec_ref(v_env_3246_);
                v___x_3273_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3272_);
                v_mod_3274_ = lean_array_get(v___x_3271_, v___x_3273_, v_val_3267_);
                leanh::lean_dec(v_val_3267_);
                leanh::lean_dec_ref(v___x_3273_);
                v___x_3275_ = l_Lean_isPrivateName(v_declHint_3242_);
                leanh::lean_dec(v_declHint_3242_);
                if v___x_3275_ == 0 {
                    v___x_3276_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11);
                    v___x_3277_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3277_, 0, v___x_3276_);
                    leanh::lean_ctor_set(v___x_3277_, 1, v_c_3258_);
                    v___x_3278_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13);
                    v___x_3279_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3279_, 0, v___x_3277_);
                    leanh::lean_ctor_set(v___x_3279_, 1, v___x_3278_);
                    v___x_3280_ = l_Lean_MessageData_ofName(v_mod_3274_);
                    v___x_3281_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3281_, 0, v___x_3279_);
                    leanh::lean_ctor_set(v___x_3281_, 1, v___x_3280_);
                    v___x_3282_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15);
                    v___x_3283_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3283_, 0, v___x_3281_);
                    leanh::lean_ctor_set(v___x_3283_, 1, v___x_3282_);
                    v___x_3284_ = l_Lean_MessageData_note(v___x_3283_);
                    v___x_3285_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3285_, 0, v_msg_3241_);
                    leanh::lean_ctor_set(v___x_3285_, 1, v___x_3284_);
                    if v_isShared_3270_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3269_, 0);
                        leanh::lean_ctor_set(v___x_3269_, 0, v___x_3285_);
                        v___x_3287_ = v___x_3269_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3288_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3288_, 0, v___x_3285_);
                        v___x_3287_ = v_reuseFailAlloc_3288_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3289_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7);
                    v___x_3290_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3290_, 0, v___x_3289_);
                    leanh::lean_ctor_set(v___x_3290_, 1, v_c_3258_);
                    v___x_3291_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17);
                    v___x_3292_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3292_, 0, v___x_3290_);
                    leanh::lean_ctor_set(v___x_3292_, 1, v___x_3291_);
                    v___x_3293_ = l_Lean_MessageData_ofName(v_mod_3274_);
                    v___x_3294_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3294_, 0, v___x_3292_);
                    leanh::lean_ctor_set(v___x_3294_, 1, v___x_3293_);
                    v___x_3295_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19);
                    v___x_3296_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3296_, 0, v___x_3294_);
                    leanh::lean_ctor_set(v___x_3296_, 1, v___x_3295_);
                    v___x_3297_ = l_Lean_MessageData_note(v___x_3296_);
                    v___x_3298_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3298_, 0, v_msg_3241_);
                    leanh::lean_ctor_set(v___x_3298_, 1, v___x_3297_);
                    if v_isShared_3270_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3269_, 0);
                        leanh::lean_ctor_set(v___x_3269_, 0, v___x_3298_);
                        v___x_3300_ = v___x_3269_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3301_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3298_);
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
    mut v_msg_3304_: *mut leanh::LeanObject,
    mut v_declHint_3305_: *mut leanh::LeanObject,
    mut v___y_3306_: *mut leanh::LeanObject,
    mut v___y_3307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3308_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(v_msg_3304_, v_declHint_3305_, v___y_3306_);
    leanh::lean_dec(v___y_3306_);
    return v_res_3308_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(
    mut v_msg_3309_: *mut leanh::LeanObject,
    mut v_declHint_3310_: *mut leanh::LeanObject,
    mut v___y_3311_: *mut leanh::LeanObject,
    mut v___y_3312_: *mut leanh::LeanObject,
    mut v___y_3313_: *mut leanh::LeanObject,
    mut v___y_3314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3320_: u8 = 0;
    let mut v___x_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3326_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3316_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(v_msg_3309_, v_declHint_3310_, v___y_3314_);
                v_a_3317_ = leanh::lean_ctor_get(v___x_3316_, 0);
                v_isSharedCheck_3326_ = (!leanh::lean_is_exclusive(v___x_3316_)) as u8;
                if v_isSharedCheck_3326_ == 0 {
                    v___x_3319_ = v___x_3316_;
                    v_isShared_3320_ = v_isSharedCheck_3326_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3317_);
                    leanh::lean_dec(v___x_3316_);
                    v___x_3319_ = leanh::lean_box(0);
                    v_isShared_3320_ = v_isSharedCheck_3326_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3321_ = l_Lean_unknownIdentifierMessageTag;
                v___x_3322_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3322_, 0, v___x_3321_);
                leanh::lean_ctor_set(v___x_3322_, 1, v_a_3317_);
                if v_isShared_3320_ == 0 {
                    leanh::lean_ctor_set(v___x_3319_, 0, v___x_3322_);
                    v___x_3324_ = v___x_3319_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3325_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3325_, 0, v___x_3322_);
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
    mut v_msg_3327_: *mut leanh::LeanObject,
    mut v_declHint_3328_: *mut leanh::LeanObject,
    mut v___y_3329_: *mut leanh::LeanObject,
    mut v___y_3330_: *mut leanh::LeanObject,
    mut v___y_3331_: *mut leanh::LeanObject,
    mut v___y_3332_: *mut leanh::LeanObject,
    mut v___y_3333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3334_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(v_msg_3327_, v_declHint_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
    leanh::lean_dec(v___y_3332_);
    leanh::lean_dec_ref(v___y_3331_);
    leanh::lean_dec(v___y_3330_);
    leanh::lean_dec_ref(v___y_3329_);
    return v_res_3334_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(
    mut v_ref_3335_: *mut leanh::LeanObject,
    mut v_msg_3336_: *mut leanh::LeanObject,
    mut v___y_3337_: *mut leanh::LeanObject,
    mut v___y_3338_: *mut leanh::LeanObject,
    mut v___y_3339_: *mut leanh::LeanObject,
    mut v___y_3340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3354_: u8 = 0;
    let mut v_cancelTk_x3f_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3356_: u8 = 0;
    let mut v_inheritedTraceOptions_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_3342_ = leanh::lean_ctor_get(v___y_3339_, 0);
    v_fileMap_3343_ = leanh::lean_ctor_get(v___y_3339_, 1);
    v_options_3344_ = leanh::lean_ctor_get(v___y_3339_, 2);
    v_currRecDepth_3345_ = leanh::lean_ctor_get(v___y_3339_, 3);
    v_maxRecDepth_3346_ = leanh::lean_ctor_get(v___y_3339_, 4);
    v_ref_3347_ = leanh::lean_ctor_get(v___y_3339_, 5);
    v_currNamespace_3348_ = leanh::lean_ctor_get(v___y_3339_, 6);
    v_openDecls_3349_ = leanh::lean_ctor_get(v___y_3339_, 7);
    v_initHeartbeats_3350_ = leanh::lean_ctor_get(v___y_3339_, 8);
    v_maxHeartbeats_3351_ = leanh::lean_ctor_get(v___y_3339_, 9);
    v_quotContext_3352_ = leanh::lean_ctor_get(v___y_3339_, 10);
    v_currMacroScope_3353_ = leanh::lean_ctor_get(v___y_3339_, 11);
    v_diag_3354_ = leanh::lean_ctor_get_uint8(
        v___y_3339_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3355_ = leanh::lean_ctor_get(v___y_3339_, 12);
    v_suppressElabErrors_3356_ = leanh::lean_ctor_get_uint8(
        v___y_3339_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3357_ = leanh::lean_ctor_get(v___y_3339_, 13);
    v_ref_3358_ = l_Lean_replaceRef(v_ref_3335_, v_ref_3347_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_3357_);
    leanh::lean_inc(v_cancelTk_x3f_3355_);
    leanh::lean_inc(v_currMacroScope_3353_);
    leanh::lean_inc(v_quotContext_3352_);
    leanh::lean_inc(v_maxHeartbeats_3351_);
    leanh::lean_inc(v_initHeartbeats_3350_);
    leanh::lean_inc(v_openDecls_3349_);
    leanh::lean_inc(v_currNamespace_3348_);
    leanh::lean_inc(v_maxRecDepth_3346_);
    leanh::lean_inc(v_currRecDepth_3345_);
    leanh::lean_inc_ref(v_options_3344_);
    leanh::lean_inc_ref(v_fileMap_3343_);
    leanh::lean_inc_ref(v_fileName_3342_);
    v___x_3359_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_3359_, 0, v_fileName_3342_);
    leanh::lean_ctor_set(v___x_3359_, 1, v_fileMap_3343_);
    leanh::lean_ctor_set(v___x_3359_, 2, v_options_3344_);
    leanh::lean_ctor_set(v___x_3359_, 3, v_currRecDepth_3345_);
    leanh::lean_ctor_set(v___x_3359_, 4, v_maxRecDepth_3346_);
    leanh::lean_ctor_set(v___x_3359_, 5, v_ref_3358_);
    leanh::lean_ctor_set(v___x_3359_, 6, v_currNamespace_3348_);
    leanh::lean_ctor_set(v___x_3359_, 7, v_openDecls_3349_);
    leanh::lean_ctor_set(v___x_3359_, 8, v_initHeartbeats_3350_);
    leanh::lean_ctor_set(v___x_3359_, 9, v_maxHeartbeats_3351_);
    leanh::lean_ctor_set(v___x_3359_, 10, v_quotContext_3352_);
    leanh::lean_ctor_set(v___x_3359_, 11, v_currMacroScope_3353_);
    leanh::lean_ctor_set(v___x_3359_, 12, v_cancelTk_x3f_3355_);
    leanh::lean_ctor_set(v___x_3359_, 13, v_inheritedTraceOptions_3357_);
    leanh::lean_ctor_set_uint8(
        v___x_3359_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_3354_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_3359_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3356_,
    );
    v___x_3360_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v_msg_3336_, v___y_3337_, v___y_3338_, v___x_3359_, v___y_3340_);
    leanh::lean_dec_ref_known(v___x_3359_, 14);
    return v___x_3360_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg___boxed(
    mut v_ref_3361_: *mut leanh::LeanObject,
    mut v_msg_3362_: *mut leanh::LeanObject,
    mut v___y_3363_: *mut leanh::LeanObject,
    mut v___y_3364_: *mut leanh::LeanObject,
    mut v___y_3365_: *mut leanh::LeanObject,
    mut v___y_3366_: *mut leanh::LeanObject,
    mut v___y_3367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3368_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(v_ref_3361_, v_msg_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
    leanh::lean_dec(v___y_3366_);
    leanh::lean_dec_ref(v___y_3365_);
    leanh::lean_dec(v___y_3364_);
    leanh::lean_dec_ref(v___y_3363_);
    leanh::lean_dec(v_ref_3361_);
    return v_res_3368_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(
    mut v_ref_3369_: *mut leanh::LeanObject,
    mut v_msg_3370_: *mut leanh::LeanObject,
    mut v_declHint_3371_: *mut leanh::LeanObject,
    mut v___y_3372_: *mut leanh::LeanObject,
    mut v___y_3373_: *mut leanh::LeanObject,
    mut v___y_3374_: *mut leanh::LeanObject,
    mut v___y_3375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3377_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(v_msg_3370_, v_declHint_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
    v_a_3378_ = leanh::lean_ctor_get(v___x_3377_, 0);
    leanh::lean_inc(v_a_3378_);
    leanh::lean_dec_ref(v___x_3377_);
    v___x_3379_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(v_ref_3369_, v_a_3378_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
    return v___x_3379_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg___boxed(
    mut v_ref_3380_: *mut leanh::LeanObject,
    mut v_msg_3381_: *mut leanh::LeanObject,
    mut v_declHint_3382_: *mut leanh::LeanObject,
    mut v___y_3383_: *mut leanh::LeanObject,
    mut v___y_3384_: *mut leanh::LeanObject,
    mut v___y_3385_: *mut leanh::LeanObject,
    mut v___y_3386_: *mut leanh::LeanObject,
    mut v___y_3387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3388_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(v_ref_3380_, v_msg_3381_, v_declHint_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_);
    leanh::lean_dec(v___y_3386_);
    leanh::lean_dec_ref(v___y_3385_);
    leanh::lean_dec(v___y_3384_);
    leanh::lean_dec_ref(v___y_3383_);
    leanh::lean_dec(v_ref_3380_);
    return v_res_3388_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3390_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0;
    v___x_3391_ = l_Lean_stringToMessageData(v___x_3390_);
    return v___x_3391_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(
    mut v_ref_3392_: *mut leanh::LeanObject,
    mut v_constName_3393_: *mut leanh::LeanObject,
    mut v___y_3394_: *mut leanh::LeanObject,
    mut v___y_3395_: *mut leanh::LeanObject,
    mut v___y_3396_: *mut leanh::LeanObject,
    mut v___y_3397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: u8 = 0;
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3399_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1);
    v___x_3400_ = 0;
    leanh::lean_inc(v_constName_3393_);
    v___x_3401_ = l_Lean_MessageData_ofConstName(v_constName_3393_, v___x_3400_);
    v___x_3402_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3402_, 0, v___x_3399_);
    leanh::lean_ctor_set(v___x_3402_, 1, v___x_3401_);
    v___x_3403_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1_once
        ),
        _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1,
    );
    v___x_3404_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3404_, 0, v___x_3402_);
    leanh::lean_ctor_set(v___x_3404_, 1, v___x_3403_);
    v___x_3405_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(v_ref_3392_, v___x_3404_, v_constName_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
    return v___x_3405_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___boxed(
    mut v_ref_3406_: *mut leanh::LeanObject,
    mut v_constName_3407_: *mut leanh::LeanObject,
    mut v___y_3408_: *mut leanh::LeanObject,
    mut v___y_3409_: *mut leanh::LeanObject,
    mut v___y_3410_: *mut leanh::LeanObject,
    mut v___y_3411_: *mut leanh::LeanObject,
    mut v___y_3412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3413_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_3406_, v_constName_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
    leanh::lean_dec(v___y_3411_);
    leanh::lean_dec_ref(v___y_3410_);
    leanh::lean_dec(v___y_3409_);
    leanh::lean_dec_ref(v___y_3408_);
    leanh::lean_dec(v_ref_3406_);
    return v_res_3413_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(
    mut v_constName_3414_: *mut leanh::LeanObject,
    mut v___y_3415_: *mut leanh::LeanObject,
    mut v___y_3416_: *mut leanh::LeanObject,
    mut v___y_3417_: *mut leanh::LeanObject,
    mut v___y_3418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_3420_ = leanh::lean_ctor_get(v___y_3417_, 5);
    v___x_3421_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_3420_, v_constName_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
    return v___x_3421_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg___boxed(
    mut v_constName_3422_: *mut leanh::LeanObject,
    mut v___y_3423_: *mut leanh::LeanObject,
    mut v___y_3424_: *mut leanh::LeanObject,
    mut v___y_3425_: *mut leanh::LeanObject,
    mut v___y_3426_: *mut leanh::LeanObject,
    mut v___y_3427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3428_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(v_constName_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
    leanh::lean_dec(v___y_3426_);
    leanh::lean_dec_ref(v___y_3425_);
    leanh::lean_dec(v___y_3424_);
    leanh::lean_dec_ref(v___y_3423_);
    return v_res_3428_;
}
pub unsafe fn l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(
    mut v_constName_3429_: *mut leanh::LeanObject,
    mut v___y_3430_: *mut leanh::LeanObject,
    mut v___y_3431_: *mut leanh::LeanObject,
    mut v___y_3432_: *mut leanh::LeanObject,
    mut v___y_3433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: u8 = 0;
    let mut v___x_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3443_: u8 = 0;
    let mut v___x_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3447_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3435_ = lean_st_ref_get(v___y_3433_);
                v_env_3436_ = leanh::lean_ctor_get(v___x_3435_, 0);
                leanh::lean_inc_ref(v_env_3436_);
                leanh::lean_dec(v___x_3435_);
                v___x_3437_ = 0;
                leanh::lean_inc(v_constName_3429_);
                v___x_3438_ =
                    l_Lean_Environment_find_x3f(v_env_3436_, v_constName_3429_, v___x_3437_);
                if leanh::lean_obj_tag(v___x_3438_) == 0 {
                    v___x_3439_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(v_constName_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_);
                    return v___x_3439_;
                } else {
                    leanh::lean_dec(v_constName_3429_);
                    v_val_3440_ = leanh::lean_ctor_get(v___x_3438_, 0);
                    v_isSharedCheck_3447_ = (!leanh::lean_is_exclusive(v___x_3438_)) as u8;
                    if v_isSharedCheck_3447_ == 0 {
                        v___x_3442_ = v___x_3438_;
                        v_isShared_3443_ = v_isSharedCheck_3447_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3440_);
                        leanh::lean_dec(v___x_3438_);
                        v___x_3442_ = leanh::lean_box(0);
                        v_isShared_3443_ = v_isSharedCheck_3447_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3443_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3442_, 0);
                    v___x_3445_ = v___x_3442_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3446_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_val_3440_);
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
    mut v_constName_3448_: *mut leanh::LeanObject,
    mut v___y_3449_: *mut leanh::LeanObject,
    mut v___y_3450_: *mut leanh::LeanObject,
    mut v___y_3451_: *mut leanh::LeanObject,
    mut v___y_3452_: *mut leanh::LeanObject,
    mut v___y_3453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3454_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(
        v_constName_3448_,
        v___y_3449_,
        v___y_3450_,
        v___y_3451_,
        v___y_3452_,
    );
    leanh::lean_dec(v___y_3452_);
    leanh::lean_dec_ref(v___y_3451_);
    leanh::lean_dec(v___y_3450_);
    leanh::lean_dec_ref(v___y_3449_);
    return v_res_3454_;
}
pub unsafe fn l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13(
    mut v___x_3455_: u8,
    mut v_x_3456_: *mut leanh::LeanObject,
    mut v___y_3457_: *mut leanh::LeanObject,
    mut v___y_3458_: *mut leanh::LeanObject,
    mut v___y_3459_: *mut leanh::LeanObject,
    mut v___y_3460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3462_: u8 = 0;
    let mut v___x_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3471_: u8 = 0;
    let mut v___y_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3474_: u8 = 0;
    let mut v_val_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: u8 = 0;
    let mut v___x_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3488_: u8 = 0;
    let mut v_a_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3492_: u8 = 0;
    let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3496_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3456_) == 0 {
                    v___x_3462_ = 1;
                    v___x_3463_ = leanh::lean_box((v___x_3462_) as usize);
                    v___x_3464_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3464_, 0, v___x_3463_);
                    return v___x_3464_;
                } else {
                    v_head_3465_ = leanh::lean_ctor_get(v_x_3456_, 0);
                    leanh::lean_inc(v_head_3465_);
                    v_tail_3466_ = leanh::lean_ctor_get(v_x_3456_, 1);
                    leanh::lean_inc(v_tail_3466_);
                    leanh::lean_dec_ref_known(v_x_3456_, 2);
                    v___x_3467_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(
                        v_head_3465_,
                        v___y_3457_,
                        v___y_3458_,
                        v___y_3459_,
                        v___y_3460_,
                    );
                    if leanh::lean_obj_tag(v___x_3467_) == 0 {
                        v_a_3468_ = leanh::lean_ctor_get(v___x_3467_, 0);
                        v_isSharedCheck_3488_ =
                            (!leanh::lean_is_exclusive(v___x_3467_)) as u8;
                        if v_isSharedCheck_3488_ == 0 {
                            v___x_3470_ = v___x_3467_;
                            v_isShared_3471_ = v_isSharedCheck_3488_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3468_);
                            leanh::lean_dec(v___x_3467_);
                            v___x_3470_ = leanh::lean_box(0);
                            v_isShared_3471_ = v_isSharedCheck_3488_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_tail_3466_);
                        v_a_3489_ = leanh::lean_ctor_get(v___x_3467_, 0);
                        v_isSharedCheck_3496_ =
                            (!leanh::lean_is_exclusive(v___x_3467_)) as u8;
                        if v_isSharedCheck_3496_ == 0 {
                            v___x_3491_ = v___x_3467_;
                            v_isShared_3492_ = v_isSharedCheck_3496_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3489_);
                            leanh::lean_dec(v___x_3467_);
                            v___x_3491_ = leanh::lean_box(0);
                            v_isShared_3492_ = v_isSharedCheck_3496_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3468_) == 6 {
                    v_val_3476_ = leanh::lean_ctor_get(v_a_3468_, 0);
                    leanh::lean_inc_ref(v_val_3476_);
                    leanh::lean_dec_ref_known(v_a_3468_, 1);
                    v_numFields_3477_ = leanh::lean_ctor_get(v_val_3476_, 4);
                    leanh::lean_inc(v_numFields_3477_);
                    leanh::lean_dec_ref(v_val_3476_);
                    v___x_3478_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3479_ = lean_nat_dec_eq(v_numFields_3477_, v___x_3478_);
                    leanh::lean_dec(v_numFields_3477_);
                    v___x_3480_ = leanh::lean_box((v___x_3479_) as usize);
                    if v_isShared_3471_ == 0 {
                        leanh::lean_ctor_set(v___x_3470_, 0, v___x_3480_);
                        v___x_3482_ = v___x_3470_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3483_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3483_, 0, v___x_3480_);
                        v___x_3482_ = v_reuseFailAlloc_3483_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3468_);
                    v___x_3484_ = leanh::lean_box((v___x_3455_) as usize);
                    if v_isShared_3471_ == 0 {
                        leanh::lean_ctor_set(v___x_3470_, 0, v___x_3484_);
                        v___x_3486_ = v___x_3470_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3487_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3484_);
                        v___x_3486_ = v_reuseFailAlloc_3487_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_a_3474_ == 0 {
                    leanh::lean_dec(v_tail_3466_);
                    return v___y_3473_;
                } else {
                    leanh::lean_dec_ref(v___y_3473_);
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
                    v_reuseFailAlloc_3495_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_a_3489_);
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
    mut v___x_3497_: *mut leanh::LeanObject,
    mut v_x_3498_: *mut leanh::LeanObject,
    mut v___y_3499_: *mut leanh::LeanObject,
    mut v___y_3500_: *mut leanh::LeanObject,
    mut v___y_3501_: *mut leanh::LeanObject,
    mut v___y_3502_: *mut leanh::LeanObject,
    mut v___y_3503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_35476__boxed_3504_: u8 = 0;
    let mut v_res_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_35476__boxed_3504_ = (leanh::lean_unbox(v___x_3497_) as u8);
    v_res_3505_ = l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13(
        v___x_35476__boxed_3504_,
        v_x_3498_,
        v___y_3499_,
        v___y_3500_,
        v___y_3501_,
        v___y_3502_,
    );
    leanh::lean_dec(v___y_3502_);
    leanh::lean_dec_ref(v___y_3501_);
    leanh::lean_dec(v___y_3500_);
    leanh::lean_dec_ref(v___y_3499_);
    return v_res_3505_;
}
pub unsafe fn l_Lean_isEnumType___at___00mkCtorIdx_spec__9(
    mut v_declName_3506_: *mut leanh::LeanObject,
    mut v___y_3507_: *mut leanh::LeanObject,
    mut v___y_3508_: *mut leanh::LeanObject,
    mut v___y_3509_: *mut leanh::LeanObject,
    mut v___y_3510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3516_: u8 = 0;
    let mut v_val_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isRec_3522_: u8 = 0;
    let mut v_isUnsafe_3523_: u8 = 0;
    let mut v_type_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: u8 = 0;
    let mut v___x_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: u8 = 0;
    let mut v___x_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: u8 = 0;
    let mut v___x_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: u8 = 0;
    let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: u8 = 0;
    let mut v___x_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: u8 = 0;
    let mut v___x_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: u8 = 0;
    let mut v___x_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3568_: u8 = 0;
    let mut v_a_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3572_: u8 = 0;
    let mut v___x_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_3512_) == 0 {
                    v_a_3513_ = leanh::lean_ctor_get(v___x_3512_, 0);
                    v_isSharedCheck_3568_ = (!leanh::lean_is_exclusive(v___x_3512_)) as u8;
                    if v_isSharedCheck_3568_ == 0 {
                        v___x_3515_ = v___x_3512_;
                        v_isShared_3516_ = v_isSharedCheck_3568_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3513_);
                        leanh::lean_dec(v___x_3512_);
                        v___x_3515_ = leanh::lean_box(0);
                        v_isShared_3516_ = v_isSharedCheck_3568_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3569_ = leanh::lean_ctor_get(v___x_3512_, 0);
                    v_isSharedCheck_3576_ = (!leanh::lean_is_exclusive(v___x_3512_)) as u8;
                    if v_isSharedCheck_3576_ == 0 {
                        v___x_3571_ = v___x_3512_;
                        v_isShared_3572_ = v_isSharedCheck_3576_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3569_);
                        leanh::lean_dec(v___x_3512_);
                        v___x_3571_ = leanh::lean_box(0);
                        v_isShared_3572_ = v_isSharedCheck_3576_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3513_) == 5 {
                    v_val_3517_ = leanh::lean_ctor_get(v_a_3513_, 0);
                    leanh::lean_inc_ref(v_val_3517_);
                    leanh::lean_dec_ref_known(v_a_3513_, 1);
                    v_toConstantVal_3518_ = leanh::lean_ctor_get(v_val_3517_, 0);
                    v_numParams_3519_ = leanh::lean_ctor_get(v_val_3517_, 1);
                    leanh::lean_inc(v_numParams_3519_);
                    v_numIndices_3520_ = leanh::lean_ctor_get(v_val_3517_, 2);
                    leanh::lean_inc(v_numIndices_3520_);
                    v_ctors_3521_ = leanh::lean_ctor_get(v_val_3517_, 4);
                    leanh::lean_inc(v_ctors_3521_);
                    v_isRec_3522_ = leanh::lean_ctor_get_uint8(
                        v_val_3517_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                    );
                    v_isUnsafe_3523_ = leanh::lean_ctor_get_uint8(
                        v_val_3517_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 6 + 1) as u32,
                    );
                    v_type_3524_ = leanh::lean_ctor_get(v_toConstantVal_3518_, 2);
                    v___x_3525_ = l_Lean_Expr_isProp(v_type_3524_);
                    if v___x_3525_ == 0 {
                        v___x_3526_ = l_Lean_InductiveVal_numTypeFormers(v_val_3517_);
                        leanh::lean_dec_ref(v_val_3517_);
                        v___x_3527_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3528_ = lean_nat_dec_eq(v___x_3526_, v___x_3527_);
                        leanh::lean_dec(v___x_3526_);
                        if v___x_3528_ == 0 {
                            leanh::lean_dec(v_ctors_3521_);
                            leanh::lean_dec(v_numIndices_3520_);
                            leanh::lean_dec(v_numParams_3519_);
                            v___x_3529_ = leanh::lean_box((v___x_3528_) as usize);
                            if v_isShared_3516_ == 0 {
                                leanh::lean_ctor_set(v___x_3515_, 0, v___x_3529_);
                                v___x_3531_ = v___x_3515_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_3532_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3529_);
                                v___x_3531_ = v_reuseFailAlloc_3532_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_3533_ = leanh::lean_unsigned_to_nat(0);
                            v___x_3534_ = lean_nat_dec_eq(v_numIndices_3520_, v___x_3533_);
                            leanh::lean_dec(v_numIndices_3520_);
                            if v___x_3534_ == 0 {
                                leanh::lean_dec(v_ctors_3521_);
                                leanh::lean_dec(v_numParams_3519_);
                                v___x_3535_ = leanh::lean_box((v___x_3534_) as usize);
                                if v_isShared_3516_ == 0 {
                                    leanh::lean_ctor_set(v___x_3515_, 0, v___x_3535_);
                                    v___x_3537_ = v___x_3515_;
                                    state = 3;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3538_ =
                                        leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    leanh::lean_ctor_set(
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
                                leanh::lean_dec(v_numParams_3519_);
                                if v___x_3539_ == 0 {
                                    leanh::lean_dec(v_ctors_3521_);
                                    v___x_3540_ = leanh::lean_box((v___x_3539_) as usize);
                                    if v_isShared_3516_ == 0 {
                                        leanh::lean_ctor_set(v___x_3515_, 0, v___x_3540_);
                                        v___x_3542_ = v___x_3515_;
                                        state = 4;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3543_ =
                                            leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                        leanh::lean_ctor_set(
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
                                                leanh::lean_del_object(v___x_3515_);
                                                v___x_3545_ = l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13(v_isUnsafe_3523_, v_ctors_3521_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
                                                return v___x_3545_;
                                            } else {
                                                leanh::lean_dec(v_ctors_3521_);
                                                v___x_3546_ = leanh::lean_box(
                                                    (v_isRec_3522_) as usize,
                                                );
                                                if v_isShared_3516_ == 0 {
                                                    leanh::lean_ctor_set(
                                                        v___x_3515_,
                                                        0,
                                                        v___x_3546_,
                                                    );
                                                    v___x_3548_ = v___x_3515_;
                                                    state = 5;
                                                    continue;
                                                } else {
                                                    v_reuseFailAlloc_3549_ =
                                                        leanh::lean_alloc_ctor(
                                                            0,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                    leanh::lean_ctor_set(
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
                                            leanh::lean_dec(v_ctors_3521_);
                                            v___x_3550_ =
                                                leanh::lean_box((v___x_3544_) as usize);
                                            if v_isShared_3516_ == 0 {
                                                leanh::lean_ctor_set(
                                                    v___x_3515_,
                                                    0,
                                                    v___x_3550_,
                                                );
                                                v___x_3552_ = v___x_3515_;
                                                state = 6;
                                                continue;
                                            } else {
                                                v_reuseFailAlloc_3553_ =
                                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                leanh::lean_ctor_set(
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
                                        leanh::lean_dec(v_ctors_3521_);
                                        v___x_3554_ =
                                            leanh::lean_box((v___x_3525_) as usize);
                                        if v_isShared_3516_ == 0 {
                                            leanh::lean_ctor_set(
                                                v___x_3515_,
                                                0,
                                                v___x_3554_,
                                            );
                                            v___x_3556_ = v___x_3515_;
                                            state = 7;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_3557_ =
                                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                            leanh::lean_ctor_set(
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
                        leanh::lean_dec(v_ctors_3521_);
                        leanh::lean_dec(v_numIndices_3520_);
                        leanh::lean_dec(v_numParams_3519_);
                        leanh::lean_dec_ref(v_val_3517_);
                        v___x_3558_ = 0;
                        v___x_3559_ = leanh::lean_box((v___x_3558_) as usize);
                        if v_isShared_3516_ == 0 {
                            leanh::lean_ctor_set(v___x_3515_, 0, v___x_3559_);
                            v___x_3561_ = v___x_3515_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_3562_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3562_, 0, v___x_3559_);
                            v___x_3561_ = v_reuseFailAlloc_3562_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_3513_);
                    v___x_3563_ = 0;
                    v___x_3564_ = leanh::lean_box((v___x_3563_) as usize);
                    if v_isShared_3516_ == 0 {
                        leanh::lean_ctor_set(v___x_3515_, 0, v___x_3564_);
                        v___x_3566_ = v___x_3515_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3567_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3567_, 0, v___x_3564_);
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
                    v_reuseFailAlloc_3575_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
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
    mut v_declName_3577_: *mut leanh::LeanObject,
    mut v___y_3578_: *mut leanh::LeanObject,
    mut v___y_3579_: *mut leanh::LeanObject,
    mut v___y_3580_: *mut leanh::LeanObject,
    mut v___y_3581_: *mut leanh::LeanObject,
    mut v___y_3582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3583_ = l_Lean_isEnumType___at___00mkCtorIdx_spec__9(
        v_declName_3577_,
        v___y_3578_,
        v___y_3579_,
        v___y_3580_,
        v___y_3581_,
    );
    leanh::lean_dec(v___y_3581_);
    leanh::lean_dec_ref(v___y_3580_);
    leanh::lean_dec(v___y_3579_);
    leanh::lean_dec_ref(v___y_3578_);
    return v_res_3583_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0(
    mut v_k_3584_: *mut leanh::LeanObject,
    mut v_b_3585_: *mut leanh::LeanObject,
    mut v___y_3586_: *mut leanh::LeanObject,
    mut v___y_3587_: *mut leanh::LeanObject,
    mut v___y_3588_: *mut leanh::LeanObject,
    mut v___y_3589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_3589_);
    leanh::lean_inc_ref(v___y_3588_);
    leanh::lean_inc(v___y_3587_);
    leanh::lean_inc_ref(v___y_3586_);
    v___x_3591_ = leanh::lean_apply_6(
        v_k_3584_,
        v_b_3585_,
        v___y_3586_,
        v___y_3587_,
        v___y_3588_,
        v___y_3589_,
        leanh::lean_box(0),
    );
    return v___x_3591_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed(
    mut v_k_3592_: *mut leanh::LeanObject,
    mut v_b_3593_: *mut leanh::LeanObject,
    mut v___y_3594_: *mut leanh::LeanObject,
    mut v___y_3595_: *mut leanh::LeanObject,
    mut v___y_3596_: *mut leanh::LeanObject,
    mut v___y_3597_: *mut leanh::LeanObject,
    mut v___y_3598_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3599_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0(v_k_3592_, v_b_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
    leanh::lean_dec(v___y_3597_);
    leanh::lean_dec_ref(v___y_3596_);
    leanh::lean_dec(v___y_3595_);
    leanh::lean_dec_ref(v___y_3594_);
    return v_res_3599_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(
    mut v_name_3600_: *mut leanh::LeanObject,
    mut v_bi_3601_: u8,
    mut v_type_3602_: *mut leanh::LeanObject,
    mut v_k_3603_: *mut leanh::LeanObject,
    mut v_kind_3604_: u8,
    mut v___y_3605_: *mut leanh::LeanObject,
    mut v___y_3606_: *mut leanh::LeanObject,
    mut v___y_3607_: *mut leanh::LeanObject,
    mut v___y_3608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3615_: u8 = 0;
    let mut v___x_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3619_: u8 = 0;
    let mut v_a_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3623_: u8 = 0;
    let mut v___x_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3627_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3610_ = leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                leanh::lean_closure_set(v___f_3610_, 0, v_k_3603_);
                v___x_3611_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    leanh::lean_box(0),
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
                if leanh::lean_obj_tag(v___x_3611_) == 0 {
                    v_a_3612_ = leanh::lean_ctor_get(v___x_3611_, 0);
                    v_isSharedCheck_3619_ = (!leanh::lean_is_exclusive(v___x_3611_)) as u8;
                    if v_isSharedCheck_3619_ == 0 {
                        v___x_3614_ = v___x_3611_;
                        v_isShared_3615_ = v_isSharedCheck_3619_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3612_);
                        leanh::lean_dec(v___x_3611_);
                        v___x_3614_ = leanh::lean_box(0);
                        v_isShared_3615_ = v_isSharedCheck_3619_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3620_ = leanh::lean_ctor_get(v___x_3611_, 0);
                    v_isSharedCheck_3627_ = (!leanh::lean_is_exclusive(v___x_3611_)) as u8;
                    if v_isSharedCheck_3627_ == 0 {
                        v___x_3622_ = v___x_3611_;
                        v_isShared_3623_ = v_isSharedCheck_3627_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3620_);
                        leanh::lean_dec(v___x_3611_);
                        v___x_3622_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3618_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3612_);
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
                    v_reuseFailAlloc_3626_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_a_3620_);
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
    mut v_name_3628_: *mut leanh::LeanObject,
    mut v_bi_3629_: *mut leanh::LeanObject,
    mut v_type_3630_: *mut leanh::LeanObject,
    mut v_k_3631_: *mut leanh::LeanObject,
    mut v_kind_3632_: *mut leanh::LeanObject,
    mut v___y_3633_: *mut leanh::LeanObject,
    mut v___y_3634_: *mut leanh::LeanObject,
    mut v___y_3635_: *mut leanh::LeanObject,
    mut v___y_3636_: *mut leanh::LeanObject,
    mut v___y_3637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_3638_: u8 = 0;
    let mut v_kind_boxed_3639_: u8 = 0;
    let mut v_res_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_3638_ = (leanh::lean_unbox(v_bi_3629_) as u8);
    v_kind_boxed_3639_ = (leanh::lean_unbox(v_kind_3632_) as u8);
    v_res_3640_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(v_name_3628_, v_bi_boxed_3638_, v_type_3630_, v_k_3631_, v_kind_boxed_3639_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_);
    leanh::lean_dec(v___y_3636_);
    leanh::lean_dec_ref(v___y_3635_);
    leanh::lean_dec(v___y_3634_);
    leanh::lean_dec_ref(v___y_3633_);
    return v_res_3640_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg(
    mut v_name_3641_: *mut leanh::LeanObject,
    mut v_type_3642_: *mut leanh::LeanObject,
    mut v_k_3643_: *mut leanh::LeanObject,
    mut v___y_3644_: *mut leanh::LeanObject,
    mut v___y_3645_: *mut leanh::LeanObject,
    mut v___y_3646_: *mut leanh::LeanObject,
    mut v___y_3647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3649_: u8 = 0;
    let mut v___x_3650_: u8 = 0;
    let mut v___x_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3649_ = 0;
    v___x_3650_ = 0;
    v___x_3651_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(v_name_3641_, v___x_3649_, v_type_3642_, v_k_3643_, v___x_3650_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
    return v___x_3651_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg___boxed(
    mut v_name_3652_: *mut leanh::LeanObject,
    mut v_type_3653_: *mut leanh::LeanObject,
    mut v_k_3654_: *mut leanh::LeanObject,
    mut v___y_3655_: *mut leanh::LeanObject,
    mut v___y_3656_: *mut leanh::LeanObject,
    mut v___y_3657_: *mut leanh::LeanObject,
    mut v___y_3658_: *mut leanh::LeanObject,
    mut v___y_3659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3660_ = l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg(
        v_name_3652_,
        v_type_3653_,
        v_k_3654_,
        v___y_3655_,
        v___y_3656_,
        v___y_3657_,
        v___y_3658_,
    );
    leanh::lean_dec(v___y_3658_);
    leanh::lean_dec_ref(v___y_3657_);
    leanh::lean_dec(v___y_3656_);
    leanh::lean_dec_ref(v___y_3655_);
    return v_res_3660_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(
    mut v_env_3661_: *mut leanh::LeanObject,
    mut v___y_3662_: *mut leanh::LeanObject,
    mut v___y_3663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3675_: u8 = 0;
    let mut v___x_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3687_: u8 = 0;
    let mut v___x_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3695_: u8 = 0;
    let mut v_unused_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3698_: u8 = 0;
    let mut v_unused_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3665_ = lean_st_ref_take(v___y_3663_);
                v_nextMacroScope_3666_ = leanh::lean_ctor_get(v___x_3665_, 1);
                v_ngen_3667_ = leanh::lean_ctor_get(v___x_3665_, 2);
                v_auxDeclNGen_3668_ = leanh::lean_ctor_get(v___x_3665_, 3);
                v_traceState_3669_ = leanh::lean_ctor_get(v___x_3665_, 4);
                v_messages_3670_ = leanh::lean_ctor_get(v___x_3665_, 6);
                v_infoState_3671_ = leanh::lean_ctor_get(v___x_3665_, 7);
                v_snapshotTasks_3672_ = leanh::lean_ctor_get(v___x_3665_, 8);
                v_isSharedCheck_3698_ = (!leanh::lean_is_exclusive(v___x_3665_)) as u8;
                if v_isSharedCheck_3698_ == 0 {
                    v_unused_3699_ = leanh::lean_ctor_get(v___x_3665_, 5);
                    leanh::lean_dec(v_unused_3699_);
                    v_unused_3700_ = leanh::lean_ctor_get(v___x_3665_, 0);
                    leanh::lean_dec(v_unused_3700_);
                    v___x_3674_ = v___x_3665_;
                    v_isShared_3675_ = v_isSharedCheck_3698_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3672_);
                    leanh::lean_inc(v_infoState_3671_);
                    leanh::lean_inc(v_messages_3670_);
                    leanh::lean_inc(v_traceState_3669_);
                    leanh::lean_inc(v_auxDeclNGen_3668_);
                    leanh::lean_inc(v_ngen_3667_);
                    leanh::lean_inc(v_nextMacroScope_3666_);
                    leanh::lean_dec(v___x_3665_);
                    v___x_3674_ = leanh::lean_box(0);
                    v_isShared_3675_ = v_isSharedCheck_3698_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3676_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once
                    ),
                    _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2,
                );
                if v_isShared_3675_ == 0 {
                    leanh::lean_ctor_set(v___x_3674_, 5, v___x_3676_);
                    leanh::lean_ctor_set(v___x_3674_, 0, v_env_3661_);
                    v___x_3678_ = v___x_3674_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3697_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_env_3661_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3697_, 1, v_nextMacroScope_3666_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3697_, 2, v_ngen_3667_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3697_, 3, v_auxDeclNGen_3668_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3697_, 4, v_traceState_3669_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3697_, 5, v___x_3676_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3697_, 6, v_messages_3670_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3697_, 7, v_infoState_3671_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3697_, 8, v_snapshotTasks_3672_);
                    v___x_3678_ = v_reuseFailAlloc_3697_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3679_ = lean_st_ref_set(v___y_3663_, v___x_3678_);
                v___x_3680_ = lean_st_ref_take(v___y_3662_);
                v_mctx_3681_ = leanh::lean_ctor_get(v___x_3680_, 0);
                v_zetaDeltaFVarIds_3682_ = leanh::lean_ctor_get(v___x_3680_, 2);
                v_postponed_3683_ = leanh::lean_ctor_get(v___x_3680_, 3);
                v_diag_3684_ = leanh::lean_ctor_get(v___x_3680_, 4);
                v_isSharedCheck_3695_ = (!leanh::lean_is_exclusive(v___x_3680_)) as u8;
                if v_isSharedCheck_3695_ == 0 {
                    v_unused_3696_ = leanh::lean_ctor_get(v___x_3680_, 1);
                    leanh::lean_dec(v_unused_3696_);
                    v___x_3686_ = v___x_3680_;
                    v_isShared_3687_ = v_isSharedCheck_3695_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_3684_);
                    leanh::lean_inc(v_postponed_3683_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_3682_);
                    leanh::lean_inc(v_mctx_3681_);
                    leanh::lean_dec(v___x_3680_);
                    v___x_3686_ = leanh::lean_box(0);
                    v_isShared_3687_ = v_isSharedCheck_3695_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3688_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once
                    ),
                    _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3,
                );
                if v_isShared_3687_ == 0 {
                    leanh::lean_ctor_set(v___x_3686_, 1, v___x_3688_);
                    v___x_3690_ = v___x_3686_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3694_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_mctx_3681_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3694_, 1, v___x_3688_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3694_,
                        2,
                        v_zetaDeltaFVarIds_3682_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3694_, 3, v_postponed_3683_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3694_, 4, v_diag_3684_);
                    v___x_3690_ = v_reuseFailAlloc_3694_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3691_ = lean_st_ref_set(v___y_3662_, v___x_3690_);
                v___x_3692_ = leanh::lean_box(0);
                v___x_3693_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3693_, 0, v___x_3692_);
                return v___x_3693_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg___boxed(
    mut v_env_3701_: *mut leanh::LeanObject,
    mut v___y_3702_: *mut leanh::LeanObject,
    mut v___y_3703_: *mut leanh::LeanObject,
    mut v___y_3704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3705_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(v_env_3701_, v___y_3702_, v___y_3703_);
    leanh::lean_dec(v___y_3703_);
    leanh::lean_dec(v___y_3702_);
    return v_res_3705_;
}
pub unsafe fn l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11(
    mut v_declName_3706_: *mut leanh::LeanObject,
    mut v_entry_3707_: *mut leanh::LeanObject,
    mut v___y_3708_: *mut leanh::LeanObject,
    mut v___y_3709_: *mut leanh::LeanObject,
    mut v___y_3710_: *mut leanh::LeanObject,
    mut v___y_3711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3720_: u8 = 0;
    let mut v___x_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3726_: u8 = 0;
    let mut v_a_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3713_ = lean_st_ref_get(v___y_3711_);
                v_env_3714_ = leanh::lean_ctor_get(v___x_3713_, 0);
                leanh::lean_inc_ref(v_env_3714_);
                leanh::lean_dec(v___x_3713_);
                v___x_3715_ = l_Lean_Linter_deprecatedAttr;
                v___x_3716_ = l_Lean_ParametricAttribute_setParam___redArg(
                    v___x_3715_,
                    v_env_3714_,
                    v_declName_3706_,
                    v_entry_3707_,
                );
                if leanh::lean_obj_tag(v___x_3716_) == 0 {
                    v_a_3717_ = leanh::lean_ctor_get(v___x_3716_, 0);
                    v_isSharedCheck_3726_ = (!leanh::lean_is_exclusive(v___x_3716_)) as u8;
                    if v_isSharedCheck_3726_ == 0 {
                        v___x_3719_ = v___x_3716_;
                        v_isShared_3720_ = v_isSharedCheck_3726_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3717_);
                        leanh::lean_dec(v___x_3716_);
                        v___x_3719_ = leanh::lean_box(0);
                        v_isShared_3720_ = v_isSharedCheck_3726_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3727_ = leanh::lean_ctor_get(v___x_3716_, 0);
                    leanh::lean_inc(v_a_3727_);
                    leanh::lean_dec_ref_known(v___x_3716_, 1);
                    v___x_3728_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(v_a_3727_, v___y_3709_, v___y_3711_);
                    return v___x_3728_;
                }
            }
            1 => {
                if v_isShared_3720_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3719_, 3);
                    v___x_3722_ = v___x_3719_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3725_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3725_, 0, v_a_3717_);
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
    mut v_declName_3729_: *mut leanh::LeanObject,
    mut v_entry_3730_: *mut leanh::LeanObject,
    mut v___y_3731_: *mut leanh::LeanObject,
    mut v___y_3732_: *mut leanh::LeanObject,
    mut v___y_3733_: *mut leanh::LeanObject,
    mut v___y_3734_: *mut leanh::LeanObject,
    mut v___y_3735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3736_ = l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11(
        v_declName_3729_,
        v_entry_3730_,
        v___y_3731_,
        v___y_3732_,
        v___y_3733_,
        v___y_3734_,
    );
    leanh::lean_dec(v___y_3734_);
    leanh::lean_dec_ref(v___y_3733_);
    leanh::lean_dec(v___y_3732_);
    leanh::lean_dec_ref(v___y_3731_);
    return v_res_3736_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(
    mut v_declName_3737_: *mut leanh::LeanObject,
    mut v_s_3738_: u8,
    mut v___y_3739_: *mut leanh::LeanObject,
    mut v___y_3740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3753_: u8 = 0;
    let mut v___x_3754_: u8 = 0;
    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3768_: u8 = 0;
    let mut v___x_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3776_: u8 = 0;
    let mut v_unused_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3779_: u8 = 0;
    let mut v_unused_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3742_ = lean_st_ref_take(v___y_3740_);
                v_env_3743_ = leanh::lean_ctor_get(v___x_3742_, 0);
                v_nextMacroScope_3744_ = leanh::lean_ctor_get(v___x_3742_, 1);
                v_ngen_3745_ = leanh::lean_ctor_get(v___x_3742_, 2);
                v_auxDeclNGen_3746_ = leanh::lean_ctor_get(v___x_3742_, 3);
                v_traceState_3747_ = leanh::lean_ctor_get(v___x_3742_, 4);
                v_messages_3748_ = leanh::lean_ctor_get(v___x_3742_, 6);
                v_infoState_3749_ = leanh::lean_ctor_get(v___x_3742_, 7);
                v_snapshotTasks_3750_ = leanh::lean_ctor_get(v___x_3742_, 8);
                v_isSharedCheck_3779_ = (!leanh::lean_is_exclusive(v___x_3742_)) as u8;
                if v_isSharedCheck_3779_ == 0 {
                    v_unused_3780_ = leanh::lean_ctor_get(v___x_3742_, 5);
                    leanh::lean_dec(v_unused_3780_);
                    v___x_3752_ = v___x_3742_;
                    v_isShared_3753_ = v_isSharedCheck_3779_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3750_);
                    leanh::lean_inc(v_infoState_3749_);
                    leanh::lean_inc(v_messages_3748_);
                    leanh::lean_inc(v_traceState_3747_);
                    leanh::lean_inc(v_auxDeclNGen_3746_);
                    leanh::lean_inc(v_ngen_3745_);
                    leanh::lean_inc(v_nextMacroScope_3744_);
                    leanh::lean_inc(v_env_3743_);
                    leanh::lean_dec(v___x_3742_);
                    v___x_3752_ = leanh::lean_box(0);
                    v_isShared_3753_ = v_isSharedCheck_3779_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3754_ = 0;
                v___x_3755_ = leanh::lean_box(0);
                v___x_3756_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(
                    v_env_3743_,
                    v_declName_3737_,
                    v_s_3738_,
                    v___x_3754_,
                    v___x_3755_,
                );
                v___x_3757_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once
                    ),
                    _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2,
                );
                if v_isShared_3753_ == 0 {
                    leanh::lean_ctor_set(v___x_3752_, 5, v___x_3757_);
                    leanh::lean_ctor_set(v___x_3752_, 0, v___x_3756_);
                    v___x_3759_ = v___x_3752_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3778_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 0, v___x_3756_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 1, v_nextMacroScope_3744_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 2, v_ngen_3745_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 3, v_auxDeclNGen_3746_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 4, v_traceState_3747_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 5, v___x_3757_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 6, v_messages_3748_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 7, v_infoState_3749_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 8, v_snapshotTasks_3750_);
                    v___x_3759_ = v_reuseFailAlloc_3778_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3760_ = lean_st_ref_set(v___y_3740_, v___x_3759_);
                v___x_3761_ = lean_st_ref_take(v___y_3739_);
                v_mctx_3762_ = leanh::lean_ctor_get(v___x_3761_, 0);
                v_zetaDeltaFVarIds_3763_ = leanh::lean_ctor_get(v___x_3761_, 2);
                v_postponed_3764_ = leanh::lean_ctor_get(v___x_3761_, 3);
                v_diag_3765_ = leanh::lean_ctor_get(v___x_3761_, 4);
                v_isSharedCheck_3776_ = (!leanh::lean_is_exclusive(v___x_3761_)) as u8;
                if v_isSharedCheck_3776_ == 0 {
                    v_unused_3777_ = leanh::lean_ctor_get(v___x_3761_, 1);
                    leanh::lean_dec(v_unused_3777_);
                    v___x_3767_ = v___x_3761_;
                    v_isShared_3768_ = v_isSharedCheck_3776_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_3765_);
                    leanh::lean_inc(v_postponed_3764_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_3763_);
                    leanh::lean_inc(v_mctx_3762_);
                    leanh::lean_dec(v___x_3761_);
                    v___x_3767_ = leanh::lean_box(0);
                    v_isShared_3768_ = v_isSharedCheck_3776_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3769_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once
                    ),
                    _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3,
                );
                if v_isShared_3768_ == 0 {
                    leanh::lean_ctor_set(v___x_3767_, 1, v___x_3769_);
                    v___x_3771_ = v___x_3767_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3775_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_mctx_3762_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 1, v___x_3769_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3775_,
                        2,
                        v_zetaDeltaFVarIds_3763_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 3, v_postponed_3764_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 4, v_diag_3765_);
                    v___x_3771_ = v_reuseFailAlloc_3775_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3772_ = lean_st_ref_set(v___y_3739_, v___x_3771_);
                v___x_3773_ = leanh::lean_box(0);
                v___x_3774_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3774_, 0, v___x_3773_);
                return v___x_3774_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg___boxed(
    mut v_declName_3781_: *mut leanh::LeanObject,
    mut v_s_3782_: *mut leanh::LeanObject,
    mut v___y_3783_: *mut leanh::LeanObject,
    mut v___y_3784_: *mut leanh::LeanObject,
    mut v___y_3785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_boxed_3786_: u8 = 0;
    let mut v_res_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_s_boxed_3786_ = (leanh::lean_unbox(v_s_3782_) as u8);
    v_res_3787_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(v_declName_3781_, v_s_boxed_3786_, v___y_3783_, v___y_3784_);
    leanh::lean_dec(v___y_3784_);
    leanh::lean_dec(v___y_3783_);
    return v_res_3787_;
}
pub unsafe fn l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10(
    mut v_declName_3788_: *mut leanh::LeanObject,
    mut v___y_3789_: *mut leanh::LeanObject,
    mut v___y_3790_: *mut leanh::LeanObject,
    mut v___y_3791_: *mut leanh::LeanObject,
    mut v___y_3792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3794_: u8 = 0;
    let mut v___x_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3794_ = 0;
    v___x_3795_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(v_declName_3788_, v___x_3794_, v___y_3790_, v___y_3792_);
    return v___x_3795_;
}
pub unsafe fn l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10___boxed(
    mut v_declName_3796_: *mut leanh::LeanObject,
    mut v___y_3797_: *mut leanh::LeanObject,
    mut v___y_3798_: *mut leanh::LeanObject,
    mut v___y_3799_: *mut leanh::LeanObject,
    mut v___y_3800_: *mut leanh::LeanObject,
    mut v___y_3801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3802_ = l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10(
        v_declName_3796_,
        v___y_3797_,
        v___y_3798_,
        v___y_3799_,
        v___y_3800_,
    );
    leanh::lean_dec(v___y_3800_);
    leanh::lean_dec_ref(v___y_3799_);
    leanh::lean_dec(v___y_3798_);
    leanh::lean_dec_ref(v___y_3797_);
    return v_res_3802_;
}
pub unsafe fn l_mkCtorIdx___lam__1(
    mut v___x_3809_: *mut leanh::LeanObject,
    mut v___x_3810_: *mut leanh::LeanObject,
    mut v_xs_3811_: *mut leanh::LeanObject,
    mut v___x_3812_: u8,
    mut v___x_3813_: u8,
    mut v_val_3814_: *mut leanh::LeanObject,
    mut v___x_3815_: *mut leanh::LeanObject,
    mut v___x_3816_: *mut leanh::LeanObject,
    mut v___x_3817_: *mut leanh::LeanObject,
    mut v___x_3818_: *mut leanh::LeanObject,
    mut v_ctors_3819_: *mut leanh::LeanObject,
    mut v___x_3820_: *mut leanh::LeanObject,
    mut v___x_3821_: *mut leanh::LeanObject,
    mut v_levelParams_3822_: *mut leanh::LeanObject,
    mut v_indName_3823_: *mut leanh::LeanObject,
    mut v___y_3824_: *mut leanh::LeanObject,
    mut v___y_3825_: *mut leanh::LeanObject,
    mut v___y_3826_: *mut leanh::LeanObject,
    mut v___y_3827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3850_: u8 = 0;
    let mut v___x_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3863_: u8 = 0;
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3879_: u8 = 0;
    let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3891_: u8 = 0;
    let mut v___x_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3898_: u8 = 0;
    let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3906_: u8 = 0;
    let mut v_unused_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3909_: u8 = 0;
    let mut v_unused_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3912_: u8 = 0;
    let mut v_unused_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3915_: u8 = 0;
    let mut v_unused_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3918_: u8 = 0;
    let mut v_unused_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: u8 = 0;
    let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: u32 = 0;
    let mut v___x_3935_: u32 = 0;
    let mut v___x_3936_: u32 = 0;
    let mut v___x_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3942_: u8 = 0;
    let mut v___x_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3956_: u8 = 0;
    let mut v___x_3957_: u8 = 0;
    let mut v___x_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3969_: u8 = 0;
    let mut v___x_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: u8 = 0;
    let mut v___x_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3987_: u8 = 0;
    let mut v___x_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4000_: u8 = 0;
    let mut v___x_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4006_: u8 = 0;
    let mut v_unused_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4009_: u8 = 0;
    let mut v_unused_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4012_: u8 = 0;
    let mut v_isSharedCheck_4013_: u8 = 0;
    let mut v_a_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4017_: u8 = 0;
    let mut v___x_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4021_: u8 = 0;
    let mut v___y_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: u8 = 0;
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4041_: u8 = 0;
    let mut v___x_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4054_: u8 = 0;
    let mut v___x_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4060_: u8 = 0;
    let mut v_unused_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4063_: u8 = 0;
    let mut v_unused_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4077_: u8 = 0;
    let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4090_: u8 = 0;
    let mut v___x_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4106_: u8 = 0;
    let mut v___x_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4118_: u8 = 0;
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: u8 = 0;
    let mut v___x_4125_: u8 = 0;
    let mut v___x_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4128_: u8 = 0;
    let mut v_unused_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4131_: u8 = 0;
    let mut v_unused_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4134_: u8 = 0;
    let mut v_unused_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4137_: u8 = 0;
    let mut v_unused_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4140_: u8 = 0;
    let mut v_a_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4144_: u8 = 0;
    let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4148_: u8 = 0;
    let mut v_a_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4152_: u8 = 0;
    let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4156_: u8 = 0;
    let mut v_a_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4160_: u8 = 0;
    let mut v___x_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4164_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v___x_3810_);
                leanh::lean_inc_ref(v___x_3809_);
                v___x_3920_ = l_Lean_mkArrow(v___x_3809_, v___x_3810_, v___y_3826_, v___y_3827_);
                if leanh::lean_obj_tag(v___x_3920_) == 0 {
                    v_a_3921_ = leanh::lean_ctor_get(v___x_3920_, 0);
                    leanh::lean_inc(v_a_3921_);
                    leanh::lean_dec_ref_known(v___x_3920_, 1);
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
                    if leanh::lean_obj_tag(v___x_3923_) == 0 {
                        v_a_3924_ = leanh::lean_ctor_get(v___x_3923_, 0);
                        leanh::lean_inc(v_a_3924_);
                        leanh::lean_dec_ref_known(v___x_3923_, 1);
                        v___x_3925_ = leanh::lean_box((v___x_3812_) as usize);
                        v___x_3926_ = leanh::lean_box((v___x_3813_) as usize);
                        v___x_3927_ = leanh::lean_box((v___x_3922_) as usize);
                        leanh::lean_inc(v___x_3816_);
                        leanh::lean_inc_ref(v_val_3814_);
                        v___f_3928_ = leanh::lean_alloc_closure(
                            l_mkCtorIdx___lam__0___boxed as *mut core::ffi::c_void,
                            18,
                            12,
                        );
                        leanh::lean_closure_set(v___f_3928_, 0, v_xs_3811_);
                        leanh::lean_closure_set(v___f_3928_, 1, v___x_3925_);
                        leanh::lean_closure_set(v___f_3928_, 2, v___x_3926_);
                        leanh::lean_closure_set(v___f_3928_, 3, v___x_3927_);
                        leanh::lean_closure_set(v___f_3928_, 4, v_val_3814_);
                        leanh::lean_closure_set(v___f_3928_, 5, v___x_3815_);
                        leanh::lean_closure_set(v___f_3928_, 6, v___x_3810_);
                        leanh::lean_closure_set(v___f_3928_, 7, v___x_3816_);
                        leanh::lean_closure_set(v___f_3928_, 8, v___x_3817_);
                        leanh::lean_closure_set(v___f_3928_, 9, v___x_3818_);
                        leanh::lean_closure_set(v___f_3928_, 10, v_ctors_3819_);
                        leanh::lean_closure_set(v___f_3928_, 11, v___x_3820_);
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
                        if leanh::lean_obj_tag(v___x_3930_) == 0 {
                            v_a_3931_ = leanh::lean_ctor_get(v___x_3930_, 0);
                            leanh::lean_inc_n(v_a_3931_, 2);
                            leanh::lean_dec_ref_known(v___x_3930_, 1);
                            v___x_3932_ = lean_st_ref_get(v___y_3827_);
                            v_env_3933_ = leanh::lean_ctor_get(v___x_3932_, 0);
                            leanh::lean_inc_ref(v_env_3933_);
                            leanh::lean_dec(v___x_3932_);
                            v___x_3934_ = l_Lean_getMaxHeight(v_env_3933_, v_a_3931_);
                            v___x_3935_ = 1;
                            v___x_3936_ = lean_uint32_add(v___x_3934_, v___x_3935_);
                            v___x_3937_ = leanh::lean_alloc_ctor(2, 0, (4) as u32);
                            leanh::lean_ctor_set_uint32(v___x_3937_, 0 as u32, v___x_3936_);
                            leanh::lean_inc(v_a_3924_);
                            leanh::lean_inc(v_levelParams_3822_);
                            leanh::lean_inc(v___x_3821_);
                            v___x_3938_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(v___x_3821_, v_levelParams_3822_, v_a_3924_, v_a_3931_, v___x_3937_, v___y_3827_);
                            v_a_3939_ = leanh::lean_ctor_get(v___x_3938_, 0);
                            v_isSharedCheck_4140_ =
                                (!leanh::lean_is_exclusive(v___x_3938_)) as u8;
                            if v_isSharedCheck_4140_ == 0 {
                                v___x_3941_ = v___x_3938_;
                                v_isShared_3942_ = v_isSharedCheck_4140_;
                                state = 12;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3939_);
                                leanh::lean_dec(v___x_3938_);
                                v___x_3941_ = leanh::lean_box(0);
                                v_isShared_3942_ = v_isSharedCheck_4140_;
                                state = 12;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_3924_);
                            leanh::lean_dec(v_indName_3823_);
                            leanh::lean_dec(v_levelParams_3822_);
                            leanh::lean_dec(v___x_3821_);
                            leanh::lean_dec(v___x_3816_);
                            leanh::lean_dec_ref(v_val_3814_);
                            v_a_4141_ = leanh::lean_ctor_get(v___x_3930_, 0);
                            v_isSharedCheck_4148_ =
                                (!leanh::lean_is_exclusive(v___x_3930_)) as u8;
                            if v_isSharedCheck_4148_ == 0 {
                                v___x_4143_ = v___x_3930_;
                                v_isShared_4144_ = v_isSharedCheck_4148_;
                                state = 38;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4141_);
                                leanh::lean_dec(v___x_3930_);
                                v___x_4143_ = leanh::lean_box(0);
                                v_isShared_4144_ = v_isSharedCheck_4148_;
                                state = 38;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_indName_3823_);
                        leanh::lean_dec(v_levelParams_3822_);
                        leanh::lean_dec(v___x_3821_);
                        leanh::lean_dec(v___x_3820_);
                        leanh::lean_dec(v_ctors_3819_);
                        leanh::lean_dec_ref(v___x_3818_);
                        leanh::lean_dec(v___x_3817_);
                        leanh::lean_dec(v___x_3816_);
                        leanh::lean_dec_ref(v___x_3815_);
                        leanh::lean_dec_ref(v_val_3814_);
                        leanh::lean_dec_ref(v_xs_3811_);
                        leanh::lean_dec_ref(v___x_3810_);
                        leanh::lean_dec_ref(v___x_3809_);
                        v_a_4149_ = leanh::lean_ctor_get(v___x_3923_, 0);
                        v_isSharedCheck_4156_ =
                            (!leanh::lean_is_exclusive(v___x_3923_)) as u8;
                        if v_isSharedCheck_4156_ == 0 {
                            v___x_4151_ = v___x_3923_;
                            v_isShared_4152_ = v_isSharedCheck_4156_;
                            state = 40;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4149_);
                            leanh::lean_dec(v___x_3923_);
                            v___x_4151_ = leanh::lean_box(0);
                            v_isShared_4152_ = v_isSharedCheck_4156_;
                            state = 40;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_indName_3823_);
                    leanh::lean_dec(v_levelParams_3822_);
                    leanh::lean_dec(v___x_3821_);
                    leanh::lean_dec(v___x_3820_);
                    leanh::lean_dec(v_ctors_3819_);
                    leanh::lean_dec_ref(v___x_3818_);
                    leanh::lean_dec(v___x_3817_);
                    leanh::lean_dec(v___x_3816_);
                    leanh::lean_dec_ref(v___x_3815_);
                    leanh::lean_dec_ref(v_val_3814_);
                    leanh::lean_dec_ref(v_xs_3811_);
                    leanh::lean_dec_ref(v___x_3810_);
                    leanh::lean_dec_ref(v___x_3809_);
                    v_a_4157_ = leanh::lean_ctor_get(v___x_3920_, 0);
                    v_isSharedCheck_4164_ = (!leanh::lean_is_exclusive(v___x_3920_)) as u8;
                    if v_isSharedCheck_4164_ == 0 {
                        v___x_4159_ = v___x_3920_;
                        v_isShared_4160_ = v_isSharedCheck_4164_;
                        state = 42;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4157_);
                        leanh::lean_dec(v___x_3920_);
                        v___x_4159_ = leanh::lean_box(0);
                        v_isShared_4160_ = v_isSharedCheck_4164_;
                        state = 42;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3835_ = leanh::lean_unsigned_to_nat(1);
                v___x_3836_ = lean_mk_empty_array_with_capacity(v___x_3835_);
                leanh::lean_inc(v___y_3830_);
                v___x_3837_ = lean_array_push(v___x_3836_, v___y_3830_);
                v___x_3838_ =
                    l_Lean_compileDecls(v___x_3837_, v___x_3813_, v___y_3833_, v___y_3834_);
                if leanh::lean_obj_tag(v___x_3838_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3838_, 1);
                    v___x_3839_ = lean_st_ref_take(v___y_3834_);
                    v_env_3840_ = leanh::lean_ctor_get(v___x_3839_, 0);
                    v_nextMacroScope_3841_ = leanh::lean_ctor_get(v___x_3839_, 1);
                    v_ngen_3842_ = leanh::lean_ctor_get(v___x_3839_, 2);
                    v_auxDeclNGen_3843_ = leanh::lean_ctor_get(v___x_3839_, 3);
                    v_traceState_3844_ = leanh::lean_ctor_get(v___x_3839_, 4);
                    v_messages_3845_ = leanh::lean_ctor_get(v___x_3839_, 6);
                    v_infoState_3846_ = leanh::lean_ctor_get(v___x_3839_, 7);
                    v_snapshotTasks_3847_ = leanh::lean_ctor_get(v___x_3839_, 8);
                    v_isSharedCheck_3918_ = (!leanh::lean_is_exclusive(v___x_3839_)) as u8;
                    if v_isSharedCheck_3918_ == 0 {
                        v_unused_3919_ = leanh::lean_ctor_get(v___x_3839_, 5);
                        leanh::lean_dec(v_unused_3919_);
                        v___x_3849_ = v___x_3839_;
                        v_isShared_3850_ = v_isSharedCheck_3918_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_3847_);
                        leanh::lean_inc(v_infoState_3846_);
                        leanh::lean_inc(v_messages_3845_);
                        leanh::lean_inc(v_traceState_3844_);
                        leanh::lean_inc(v_auxDeclNGen_3843_);
                        leanh::lean_inc(v_ngen_3842_);
                        leanh::lean_inc(v_nextMacroScope_3841_);
                        leanh::lean_inc(v_env_3840_);
                        leanh::lean_dec(v___x_3839_);
                        v___x_3849_ = leanh::lean_box(0);
                        v_isShared_3850_ = v_isSharedCheck_3918_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_3830_);
                    leanh::lean_dec(v___x_3821_);
                    return v___x_3838_;
                }
            }
            2 => {
                leanh::lean_inc(v___y_3830_);
                v___x_3851_ = l_Lean_Meta_addToCompletionBlackList(v_env_3840_, v___y_3830_);
                v___x_3852_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once
                    ),
                    _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2,
                );
                if v_isShared_3850_ == 0 {
                    leanh::lean_ctor_set(v___x_3849_, 5, v___x_3852_);
                    leanh::lean_ctor_set(v___x_3849_, 0, v___x_3851_);
                    v___x_3854_ = v___x_3849_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3917_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3917_, 0, v___x_3851_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3917_, 1, v_nextMacroScope_3841_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3917_, 2, v_ngen_3842_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3917_, 3, v_auxDeclNGen_3843_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3917_, 4, v_traceState_3844_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3917_, 5, v___x_3852_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3917_, 6, v_messages_3845_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3917_, 7, v_infoState_3846_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3917_, 8, v_snapshotTasks_3847_);
                    v___x_3854_ = v_reuseFailAlloc_3917_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3855_ = lean_st_ref_set(v___y_3834_, v___x_3854_);
                v___x_3856_ = lean_st_ref_take(v___y_3832_);
                v_mctx_3857_ = leanh::lean_ctor_get(v___x_3856_, 0);
                v_zetaDeltaFVarIds_3858_ = leanh::lean_ctor_get(v___x_3856_, 2);
                v_postponed_3859_ = leanh::lean_ctor_get(v___x_3856_, 3);
                v_diag_3860_ = leanh::lean_ctor_get(v___x_3856_, 4);
                v_isSharedCheck_3915_ = (!leanh::lean_is_exclusive(v___x_3856_)) as u8;
                if v_isSharedCheck_3915_ == 0 {
                    v_unused_3916_ = leanh::lean_ctor_get(v___x_3856_, 1);
                    leanh::lean_dec(v_unused_3916_);
                    v___x_3862_ = v___x_3856_;
                    v_isShared_3863_ = v_isSharedCheck_3915_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_3860_);
                    leanh::lean_inc(v_postponed_3859_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_3858_);
                    leanh::lean_inc(v_mctx_3857_);
                    leanh::lean_dec(v___x_3856_);
                    v___x_3862_ = leanh::lean_box(0);
                    v_isShared_3863_ = v_isSharedCheck_3915_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3864_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once
                    ),
                    _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3,
                );
                if v_isShared_3863_ == 0 {
                    leanh::lean_ctor_set(v___x_3862_, 1, v___x_3864_);
                    v___x_3866_ = v___x_3862_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3914_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_mctx_3857_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3914_, 1, v___x_3864_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3914_,
                        2,
                        v_zetaDeltaFVarIds_3858_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3914_, 3, v_postponed_3859_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3914_, 4, v_diag_3860_);
                    v___x_3866_ = v_reuseFailAlloc_3914_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3867_ = lean_st_ref_set(v___y_3832_, v___x_3866_);
                v___x_3868_ = lean_st_ref_take(v___y_3834_);
                v_env_3869_ = leanh::lean_ctor_get(v___x_3868_, 0);
                v_nextMacroScope_3870_ = leanh::lean_ctor_get(v___x_3868_, 1);
                v_ngen_3871_ = leanh::lean_ctor_get(v___x_3868_, 2);
                v_auxDeclNGen_3872_ = leanh::lean_ctor_get(v___x_3868_, 3);
                v_traceState_3873_ = leanh::lean_ctor_get(v___x_3868_, 4);
                v_messages_3874_ = leanh::lean_ctor_get(v___x_3868_, 6);
                v_infoState_3875_ = leanh::lean_ctor_get(v___x_3868_, 7);
                v_snapshotTasks_3876_ = leanh::lean_ctor_get(v___x_3868_, 8);
                v_isSharedCheck_3912_ = (!leanh::lean_is_exclusive(v___x_3868_)) as u8;
                if v_isSharedCheck_3912_ == 0 {
                    v_unused_3913_ = leanh::lean_ctor_get(v___x_3868_, 5);
                    leanh::lean_dec(v_unused_3913_);
                    v___x_3878_ = v___x_3868_;
                    v_isShared_3879_ = v_isSharedCheck_3912_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3876_);
                    leanh::lean_inc(v_infoState_3875_);
                    leanh::lean_inc(v_messages_3874_);
                    leanh::lean_inc(v_traceState_3873_);
                    leanh::lean_inc(v_auxDeclNGen_3872_);
                    leanh::lean_inc(v_ngen_3871_);
                    leanh::lean_inc(v_nextMacroScope_3870_);
                    leanh::lean_inc(v_env_3869_);
                    leanh::lean_dec(v___x_3868_);
                    v___x_3878_ = leanh::lean_box(0);
                    v_isShared_3879_ = v_isSharedCheck_3912_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                leanh::lean_inc(v___y_3830_);
                v___x_3880_ = l_Lean_addProtected(v_env_3869_, v___y_3830_);
                if v_isShared_3879_ == 0 {
                    leanh::lean_ctor_set(v___x_3878_, 5, v___x_3852_);
                    leanh::lean_ctor_set(v___x_3878_, 0, v___x_3880_);
                    v___x_3882_ = v___x_3878_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3911_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 0, v___x_3880_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 1, v_nextMacroScope_3870_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 2, v_ngen_3871_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 3, v_auxDeclNGen_3872_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 4, v_traceState_3873_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 5, v___x_3852_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 6, v_messages_3874_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 7, v_infoState_3875_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3911_, 8, v_snapshotTasks_3876_);
                    v___x_3882_ = v_reuseFailAlloc_3911_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3883_ = lean_st_ref_set(v___y_3834_, v___x_3882_);
                v___x_3884_ = lean_st_ref_take(v___y_3832_);
                v_mctx_3885_ = leanh::lean_ctor_get(v___x_3884_, 0);
                v_zetaDeltaFVarIds_3886_ = leanh::lean_ctor_get(v___x_3884_, 2);
                v_postponed_3887_ = leanh::lean_ctor_get(v___x_3884_, 3);
                v_diag_3888_ = leanh::lean_ctor_get(v___x_3884_, 4);
                v_isSharedCheck_3909_ = (!leanh::lean_is_exclusive(v___x_3884_)) as u8;
                if v_isSharedCheck_3909_ == 0 {
                    v_unused_3910_ = leanh::lean_ctor_get(v___x_3884_, 1);
                    leanh::lean_dec(v_unused_3910_);
                    v___x_3890_ = v___x_3884_;
                    v_isShared_3891_ = v_isSharedCheck_3909_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_3888_);
                    leanh::lean_inc(v_postponed_3887_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_3886_);
                    leanh::lean_inc(v_mctx_3885_);
                    leanh::lean_dec(v___x_3884_);
                    v___x_3890_ = leanh::lean_box(0);
                    v_isShared_3891_ = v_isSharedCheck_3909_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_3891_ == 0 {
                    leanh::lean_ctor_set(v___x_3890_, 1, v___x_3864_);
                    v___x_3893_ = v___x_3890_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3908_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_mctx_3885_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3908_, 1, v___x_3864_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3908_,
                        2,
                        v_zetaDeltaFVarIds_3886_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3908_, 3, v_postponed_3887_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3908_, 4, v_diag_3888_);
                    v___x_3893_ = v_reuseFailAlloc_3908_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3894_ = lean_st_ref_set(v___y_3832_, v___x_3893_);
                leanh::lean_inc(v___y_3830_);
                v___x_3895_ = l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10(
                    v___y_3830_,
                    v___y_3831_,
                    v___y_3832_,
                    v___y_3833_,
                    v___y_3834_,
                );
                v_isSharedCheck_3906_ = (!leanh::lean_is_exclusive(v___x_3895_)) as u8;
                if v_isSharedCheck_3906_ == 0 {
                    v_unused_3907_ = leanh::lean_ctor_get(v___x_3895_, 0);
                    leanh::lean_dec(v_unused_3907_);
                    v___x_3897_ = v___x_3895_;
                    v_isShared_3898_ = v_isSharedCheck_3906_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_dec(v___x_3895_);
                    v___x_3897_ = leanh::lean_box(0);
                    v_isShared_3898_ = v_isSharedCheck_3906_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_3898_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3897_, 1);
                    leanh::lean_ctor_set(v___x_3897_, 0, v___x_3821_);
                    v___x_3900_ = v___x_3897_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3905_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3905_, 0, v___x_3821_);
                    v___x_3900_ = v_reuseFailAlloc_3905_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_3901_ = leanh::lean_box(0);
                v___x_3902_ = l_mkCtorIdx___lam__1___closed__1;
                v___x_3903_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3903_, 0, v___x_3900_);
                leanh::lean_ctor_set(v___x_3903_, 1, v___x_3901_);
                leanh::lean_ctor_set(v___x_3903_, 2, v___x_3902_);
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
                    leanh::lean_ctor_set_tag(v___x_3941_, 1);
                    v___x_3944_ = v___x_3941_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4139_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4139_, 0, v_a_3939_);
                    v___x_3944_ = v_reuseFailAlloc_4139_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                leanh::lean_inc_ref(v___x_3944_);
                v___x_4065_ = l_Lean_addDecl(v___x_3944_, v___x_3812_, v___y_3826_, v___y_3827_);
                if leanh::lean_obj_tag(v___x_4065_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4065_, 1);
                    v___x_4066_ = lean_st_ref_take(v___y_3827_);
                    v_env_4067_ = leanh::lean_ctor_get(v___x_4066_, 0);
                    v_nextMacroScope_4068_ = leanh::lean_ctor_get(v___x_4066_, 1);
                    v_ngen_4069_ = leanh::lean_ctor_get(v___x_4066_, 2);
                    v_auxDeclNGen_4070_ = leanh::lean_ctor_get(v___x_4066_, 3);
                    v_traceState_4071_ = leanh::lean_ctor_get(v___x_4066_, 4);
                    v_messages_4072_ = leanh::lean_ctor_get(v___x_4066_, 6);
                    v_infoState_4073_ = leanh::lean_ctor_get(v___x_4066_, 7);
                    v_snapshotTasks_4074_ = leanh::lean_ctor_get(v___x_4066_, 8);
                    v_isSharedCheck_4137_ = (!leanh::lean_is_exclusive(v___x_4066_)) as u8;
                    if v_isSharedCheck_4137_ == 0 {
                        v_unused_4138_ = leanh::lean_ctor_get(v___x_4066_, 5);
                        leanh::lean_dec(v_unused_4138_);
                        v___x_4076_ = v___x_4066_;
                        v_isShared_4077_ = v_isSharedCheck_4137_;
                        state = 30;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_4074_);
                        leanh::lean_inc(v_infoState_4073_);
                        leanh::lean_inc(v_messages_4072_);
                        leanh::lean_inc(v_traceState_4071_);
                        leanh::lean_inc(v_auxDeclNGen_4070_);
                        leanh::lean_inc(v_ngen_4069_);
                        leanh::lean_inc(v_nextMacroScope_4068_);
                        leanh::lean_inc(v_env_4067_);
                        leanh::lean_dec(v___x_4066_);
                        v___x_4076_ = leanh::lean_box(0);
                        v_isShared_4077_ = v_isSharedCheck_4137_;
                        state = 30;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_3944_);
                    leanh::lean_dec(v_a_3924_);
                    leanh::lean_dec(v_indName_3823_);
                    leanh::lean_dec(v_levelParams_3822_);
                    leanh::lean_dec(v___x_3821_);
                    leanh::lean_dec(v___x_3816_);
                    leanh::lean_dec_ref(v_val_3814_);
                    return v___x_4065_;
                }
            }
            14 => {
                v___x_3950_ =
                    l_Lean_compileDecl(v___x_3944_, v___x_3813_, v___y_3948_, v___y_3949_);
                if leanh::lean_obj_tag(v___x_3950_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3950_, 1);
                    leanh::lean_inc(v___x_3821_);
                    v___x_3951_ =
                        l_Lean_enableRealizationsForConst(v___x_3821_, v___y_3948_, v___y_3949_);
                    if leanh::lean_obj_tag(v___x_3951_) == 0 {
                        leanh::lean_dec_ref_known(v___x_3951_, 1);
                        leanh::lean_inc(v_indName_3823_);
                        v___x_3952_ = l_Lean_isEnumType___at___00mkCtorIdx_spec__9(
                            v_indName_3823_,
                            v___y_3946_,
                            v___y_3947_,
                            v___y_3948_,
                            v___y_3949_,
                        );
                        if leanh::lean_obj_tag(v___x_3952_) == 0 {
                            v_a_3953_ = leanh::lean_ctor_get(v___x_3952_, 0);
                            v_isSharedCheck_4013_ =
                                (!leanh::lean_is_exclusive(v___x_3952_)) as u8;
                            if v_isSharedCheck_4013_ == 0 {
                                v___x_3955_ = v___x_3952_;
                                v_isShared_3956_ = v_isSharedCheck_4013_;
                                state = 15;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3953_);
                                leanh::lean_dec(v___x_3952_);
                                v___x_3955_ = leanh::lean_box(0);
                                v_isShared_3956_ = v_isSharedCheck_4013_;
                                state = 15;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_3924_);
                            leanh::lean_dec(v_indName_3823_);
                            leanh::lean_dec(v_levelParams_3822_);
                            leanh::lean_dec(v___x_3821_);
                            leanh::lean_dec(v___x_3816_);
                            v_a_4014_ = leanh::lean_ctor_get(v___x_3952_, 0);
                            v_isSharedCheck_4021_ =
                                (!leanh::lean_is_exclusive(v___x_3952_)) as u8;
                            if v_isSharedCheck_4021_ == 0 {
                                v___x_4016_ = v___x_3952_;
                                v_isShared_4017_ = v_isSharedCheck_4021_;
                                state = 23;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4014_);
                                leanh::lean_dec(v___x_3952_);
                                v___x_4016_ = leanh::lean_box(0);
                                v_isShared_4017_ = v_isSharedCheck_4021_;
                                state = 23;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_3924_);
                        leanh::lean_dec(v_indName_3823_);
                        leanh::lean_dec(v_levelParams_3822_);
                        leanh::lean_dec(v___x_3821_);
                        leanh::lean_dec(v___x_3816_);
                        return v___x_3951_;
                    }
                } else {
                    leanh::lean_dec(v_a_3924_);
                    leanh::lean_dec(v_indName_3823_);
                    leanh::lean_dec(v_levelParams_3822_);
                    leanh::lean_dec(v___x_3821_);
                    leanh::lean_dec(v___x_3816_);
                    return v___x_3950_;
                }
            }
            15 => {
                v___x_3957_ = (leanh::lean_unbox(v_a_3953_) as u8);
                leanh::lean_dec(v_a_3953_);
                if v___x_3957_ == 0 {
                    leanh::lean_dec(v_a_3924_);
                    leanh::lean_dec(v_indName_3823_);
                    leanh::lean_dec(v_levelParams_3822_);
                    leanh::lean_dec(v___x_3821_);
                    leanh::lean_dec(v___x_3816_);
                    v___x_3958_ = leanh::lean_box(0);
                    if v_isShared_3956_ == 0 {
                        leanh::lean_ctor_set(v___x_3955_, 0, v___x_3958_);
                        v___x_3960_ = v___x_3955_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_3961_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3961_, 0, v___x_3958_);
                        v___x_3960_ = v_reuseFailAlloc_3961_;
                        state = 16;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3955_);
                    leanh::lean_inc(v_indName_3823_);
                    v___x_3962_ = l_mkToCtorIdxName(v_indName_3823_);
                    leanh::lean_inc(v___x_3821_);
                    v___x_3963_ = l_Lean_mkConst(v___x_3821_, v___x_3816_);
                    v___x_3964_ = leanh::lean_box(1);
                    leanh::lean_inc(v___x_3962_);
                    v___x_3965_ =
                        l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(
                            v___x_3962_,
                            v_levelParams_3822_,
                            v_a_3924_,
                            v___x_3963_,
                            v___x_3964_,
                            v___y_3949_,
                        );
                    v_a_3966_ = leanh::lean_ctor_get(v___x_3965_, 0);
                    v_isSharedCheck_4012_ = (!leanh::lean_is_exclusive(v___x_3965_)) as u8;
                    if v_isSharedCheck_4012_ == 0 {
                        v___x_3968_ = v___x_3965_;
                        v_isShared_3969_ = v_isSharedCheck_4012_;
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3966_);
                        leanh::lean_dec(v___x_3965_);
                        v___x_3968_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set_tag(v___x_3968_, 1);
                    v___x_3971_ = v___x_3968_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4011_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_a_3966_);
                    v___x_3971_ = v_reuseFailAlloc_4011_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_3972_ = l_Lean_addDecl(v___x_3971_, v___x_3812_, v___y_3948_, v___y_3949_);
                if leanh::lean_obj_tag(v___x_3972_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3972_, 1);
                    v___x_3973_ = lean_st_ref_get(v___y_3949_);
                    v_env_3974_ = leanh::lean_ctor_get(v___x_3973_, 0);
                    leanh::lean_inc_ref(v_env_3974_);
                    leanh::lean_dec(v___x_3973_);
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
                        v_env_3977_ = leanh::lean_ctor_get(v___x_3976_, 0);
                        v_nextMacroScope_3978_ = leanh::lean_ctor_get(v___x_3976_, 1);
                        v_ngen_3979_ = leanh::lean_ctor_get(v___x_3976_, 2);
                        v_auxDeclNGen_3980_ = leanh::lean_ctor_get(v___x_3976_, 3);
                        v_traceState_3981_ = leanh::lean_ctor_get(v___x_3976_, 4);
                        v_messages_3982_ = leanh::lean_ctor_get(v___x_3976_, 6);
                        v_infoState_3983_ = leanh::lean_ctor_get(v___x_3976_, 7);
                        v_snapshotTasks_3984_ = leanh::lean_ctor_get(v___x_3976_, 8);
                        v_isSharedCheck_4009_ =
                            (!leanh::lean_is_exclusive(v___x_3976_)) as u8;
                        if v_isSharedCheck_4009_ == 0 {
                            v_unused_4010_ = leanh::lean_ctor_get(v___x_3976_, 5);
                            leanh::lean_dec(v_unused_4010_);
                            v___x_3986_ = v___x_3976_;
                            v_isShared_3987_ = v_isSharedCheck_4009_;
                            state = 19;
                            continue;
                        } else {
                            leanh::lean_inc(v_snapshotTasks_3984_);
                            leanh::lean_inc(v_infoState_3983_);
                            leanh::lean_inc(v_messages_3982_);
                            leanh::lean_inc(v_traceState_3981_);
                            leanh::lean_inc(v_auxDeclNGen_3980_);
                            leanh::lean_inc(v_ngen_3979_);
                            leanh::lean_inc(v_nextMacroScope_3978_);
                            leanh::lean_inc(v_env_3977_);
                            leanh::lean_dec(v___x_3976_);
                            v___x_3986_ = leanh::lean_box(0);
                            v_isShared_3987_ = v_isSharedCheck_4009_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_3962_);
                    leanh::lean_dec(v_indName_3823_);
                    leanh::lean_dec(v___x_3821_);
                    return v___x_3972_;
                }
            }
            19 => {
                leanh::lean_inc(v___x_3962_);
                v___x_3988_ = l_Lean_markMeta(v_env_3977_, v___x_3962_);
                v___x_3989_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once
                    ),
                    _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2,
                );
                if v_isShared_3987_ == 0 {
                    leanh::lean_ctor_set(v___x_3986_, 5, v___x_3989_);
                    leanh::lean_ctor_set(v___x_3986_, 0, v___x_3988_);
                    v___x_3991_ = v___x_3986_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4008_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4008_, 0, v___x_3988_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4008_, 1, v_nextMacroScope_3978_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4008_, 2, v_ngen_3979_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4008_, 3, v_auxDeclNGen_3980_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4008_, 4, v_traceState_3981_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4008_, 5, v___x_3989_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4008_, 6, v_messages_3982_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4008_, 7, v_infoState_3983_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4008_, 8, v_snapshotTasks_3984_);
                    v___x_3991_ = v_reuseFailAlloc_4008_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_3992_ = lean_st_ref_set(v___y_3949_, v___x_3991_);
                v___x_3993_ = lean_st_ref_take(v___y_3947_);
                v_mctx_3994_ = leanh::lean_ctor_get(v___x_3993_, 0);
                v_zetaDeltaFVarIds_3995_ = leanh::lean_ctor_get(v___x_3993_, 2);
                v_postponed_3996_ = leanh::lean_ctor_get(v___x_3993_, 3);
                v_diag_3997_ = leanh::lean_ctor_get(v___x_3993_, 4);
                v_isSharedCheck_4006_ = (!leanh::lean_is_exclusive(v___x_3993_)) as u8;
                if v_isSharedCheck_4006_ == 0 {
                    v_unused_4007_ = leanh::lean_ctor_get(v___x_3993_, 1);
                    leanh::lean_dec(v_unused_4007_);
                    v___x_3999_ = v___x_3993_;
                    v_isShared_4000_ = v_isSharedCheck_4006_;
                    state = 21;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_3997_);
                    leanh::lean_inc(v_postponed_3996_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_3995_);
                    leanh::lean_inc(v_mctx_3994_);
                    leanh::lean_dec(v___x_3993_);
                    v___x_3999_ = leanh::lean_box(0);
                    v_isShared_4000_ = v_isSharedCheck_4006_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_4001_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once
                    ),
                    _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3,
                );
                if v_isShared_4000_ == 0 {
                    leanh::lean_ctor_set(v___x_3999_, 1, v___x_4001_);
                    v___x_4003_ = v___x_3999_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4005_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_mctx_3994_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4005_, 1, v___x_4001_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4005_,
                        2,
                        v_zetaDeltaFVarIds_3995_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4005_, 3, v_postponed_3996_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4005_, 4, v_diag_3997_);
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
                    v_reuseFailAlloc_4020_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4020_, 0, v_a_4014_);
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
                v_env_4028_ = leanh::lean_ctor_get(v___x_4027_, 0);
                leanh::lean_inc_ref(v_env_4028_);
                leanh::lean_dec(v___x_4027_);
                leanh::lean_inc(v_indName_3823_);
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
                    v_env_4031_ = leanh::lean_ctor_get(v___x_4030_, 0);
                    v_nextMacroScope_4032_ = leanh::lean_ctor_get(v___x_4030_, 1);
                    v_ngen_4033_ = leanh::lean_ctor_get(v___x_4030_, 2);
                    v_auxDeclNGen_4034_ = leanh::lean_ctor_get(v___x_4030_, 3);
                    v_traceState_4035_ = leanh::lean_ctor_get(v___x_4030_, 4);
                    v_messages_4036_ = leanh::lean_ctor_get(v___x_4030_, 6);
                    v_infoState_4037_ = leanh::lean_ctor_get(v___x_4030_, 7);
                    v_snapshotTasks_4038_ = leanh::lean_ctor_get(v___x_4030_, 8);
                    v_isSharedCheck_4063_ = (!leanh::lean_is_exclusive(v___x_4030_)) as u8;
                    if v_isSharedCheck_4063_ == 0 {
                        v_unused_4064_ = leanh::lean_ctor_get(v___x_4030_, 5);
                        leanh::lean_dec(v_unused_4064_);
                        v___x_4040_ = v___x_4030_;
                        v_isShared_4041_ = v_isSharedCheck_4063_;
                        state = 26;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_4038_);
                        leanh::lean_inc(v_infoState_4037_);
                        leanh::lean_inc(v_messages_4036_);
                        leanh::lean_inc(v_traceState_4035_);
                        leanh::lean_inc(v_auxDeclNGen_4034_);
                        leanh::lean_inc(v_ngen_4033_);
                        leanh::lean_inc(v_nextMacroScope_4032_);
                        leanh::lean_inc(v_env_4031_);
                        leanh::lean_dec(v___x_4030_);
                        v___x_4040_ = leanh::lean_box(0);
                        v_isShared_4041_ = v_isSharedCheck_4063_;
                        state = 26;
                        continue;
                    }
                }
            }
            26 => {
                leanh::lean_inc(v___x_3821_);
                v___x_4042_ = l_Lean_markMeta(v_env_4031_, v___x_3821_);
                v___x_4043_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once
                    ),
                    _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2,
                );
                if v_isShared_4041_ == 0 {
                    leanh::lean_ctor_set(v___x_4040_, 5, v___x_4043_);
                    leanh::lean_ctor_set(v___x_4040_, 0, v___x_4042_);
                    v___x_4045_ = v___x_4040_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_4062_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 0, v___x_4042_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 1, v_nextMacroScope_4032_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 2, v_ngen_4033_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 3, v_auxDeclNGen_4034_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 4, v_traceState_4035_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 5, v___x_4043_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 6, v_messages_4036_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 7, v_infoState_4037_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 8, v_snapshotTasks_4038_);
                    v___x_4045_ = v_reuseFailAlloc_4062_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                v___x_4046_ = lean_st_ref_set(v___y_4026_, v___x_4045_);
                v___x_4047_ = lean_st_ref_take(v___y_4024_);
                v_mctx_4048_ = leanh::lean_ctor_get(v___x_4047_, 0);
                v_zetaDeltaFVarIds_4049_ = leanh::lean_ctor_get(v___x_4047_, 2);
                v_postponed_4050_ = leanh::lean_ctor_get(v___x_4047_, 3);
                v_diag_4051_ = leanh::lean_ctor_get(v___x_4047_, 4);
                v_isSharedCheck_4060_ = (!leanh::lean_is_exclusive(v___x_4047_)) as u8;
                if v_isSharedCheck_4060_ == 0 {
                    v_unused_4061_ = leanh::lean_ctor_get(v___x_4047_, 1);
                    leanh::lean_dec(v_unused_4061_);
                    v___x_4053_ = v___x_4047_;
                    v_isShared_4054_ = v_isSharedCheck_4060_;
                    state = 28;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_4051_);
                    leanh::lean_inc(v_postponed_4050_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_4049_);
                    leanh::lean_inc(v_mctx_4048_);
                    leanh::lean_dec(v___x_4047_);
                    v___x_4053_ = leanh::lean_box(0);
                    v_isShared_4054_ = v_isSharedCheck_4060_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___x_4055_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once
                    ),
                    _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3,
                );
                if v_isShared_4054_ == 0 {
                    leanh::lean_ctor_set(v___x_4053_, 1, v___x_4055_);
                    v___x_4057_ = v___x_4053_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_4059_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_mctx_4048_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4059_, 1, v___x_4055_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4059_,
                        2,
                        v_zetaDeltaFVarIds_4049_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4059_, 3, v_postponed_4050_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4059_, 4, v_diag_4051_);
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
                leanh::lean_inc(v___x_3821_);
                v___x_4078_ = l_Lean_Meta_addToCompletionBlackList(v_env_4067_, v___x_3821_);
                v___x_4079_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once
                    ),
                    _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2,
                );
                if v_isShared_4077_ == 0 {
                    leanh::lean_ctor_set(v___x_4076_, 5, v___x_4079_);
                    leanh::lean_ctor_set(v___x_4076_, 0, v___x_4078_);
                    v___x_4081_ = v___x_4076_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_4136_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 0, v___x_4078_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 1, v_nextMacroScope_4068_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 2, v_ngen_4069_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 3, v_auxDeclNGen_4070_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 4, v_traceState_4071_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 5, v___x_4079_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 6, v_messages_4072_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 7, v_infoState_4073_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 8, v_snapshotTasks_4074_);
                    v___x_4081_ = v_reuseFailAlloc_4136_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                v___x_4082_ = lean_st_ref_set(v___y_3827_, v___x_4081_);
                v___x_4083_ = lean_st_ref_take(v___y_3825_);
                v_mctx_4084_ = leanh::lean_ctor_get(v___x_4083_, 0);
                v_zetaDeltaFVarIds_4085_ = leanh::lean_ctor_get(v___x_4083_, 2);
                v_postponed_4086_ = leanh::lean_ctor_get(v___x_4083_, 3);
                v_diag_4087_ = leanh::lean_ctor_get(v___x_4083_, 4);
                v_isSharedCheck_4134_ = (!leanh::lean_is_exclusive(v___x_4083_)) as u8;
                if v_isSharedCheck_4134_ == 0 {
                    v_unused_4135_ = leanh::lean_ctor_get(v___x_4083_, 1);
                    leanh::lean_dec(v_unused_4135_);
                    v___x_4089_ = v___x_4083_;
                    v_isShared_4090_ = v_isSharedCheck_4134_;
                    state = 32;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_4087_);
                    leanh::lean_inc(v_postponed_4086_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_4085_);
                    leanh::lean_inc(v_mctx_4084_);
                    leanh::lean_dec(v___x_4083_);
                    v___x_4089_ = leanh::lean_box(0);
                    v_isShared_4090_ = v_isSharedCheck_4134_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                v___x_4091_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once
                    ),
                    _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3,
                );
                if v_isShared_4090_ == 0 {
                    leanh::lean_ctor_set(v___x_4089_, 1, v___x_4091_);
                    v___x_4093_ = v___x_4089_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_4133_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_mctx_4084_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4133_, 1, v___x_4091_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4133_,
                        2,
                        v_zetaDeltaFVarIds_4085_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4133_, 3, v_postponed_4086_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4133_, 4, v_diag_4087_);
                    v___x_4093_ = v_reuseFailAlloc_4133_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                v___x_4094_ = lean_st_ref_set(v___y_3825_, v___x_4093_);
                v___x_4095_ = lean_st_ref_take(v___y_3827_);
                v_env_4096_ = leanh::lean_ctor_get(v___x_4095_, 0);
                v_nextMacroScope_4097_ = leanh::lean_ctor_get(v___x_4095_, 1);
                v_ngen_4098_ = leanh::lean_ctor_get(v___x_4095_, 2);
                v_auxDeclNGen_4099_ = leanh::lean_ctor_get(v___x_4095_, 3);
                v_traceState_4100_ = leanh::lean_ctor_get(v___x_4095_, 4);
                v_messages_4101_ = leanh::lean_ctor_get(v___x_4095_, 6);
                v_infoState_4102_ = leanh::lean_ctor_get(v___x_4095_, 7);
                v_snapshotTasks_4103_ = leanh::lean_ctor_get(v___x_4095_, 8);
                v_isSharedCheck_4131_ = (!leanh::lean_is_exclusive(v___x_4095_)) as u8;
                if v_isSharedCheck_4131_ == 0 {
                    v_unused_4132_ = leanh::lean_ctor_get(v___x_4095_, 5);
                    leanh::lean_dec(v_unused_4132_);
                    v___x_4105_ = v___x_4095_;
                    v_isShared_4106_ = v_isSharedCheck_4131_;
                    state = 34;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4103_);
                    leanh::lean_inc(v_infoState_4102_);
                    leanh::lean_inc(v_messages_4101_);
                    leanh::lean_inc(v_traceState_4100_);
                    leanh::lean_inc(v_auxDeclNGen_4099_);
                    leanh::lean_inc(v_ngen_4098_);
                    leanh::lean_inc(v_nextMacroScope_4097_);
                    leanh::lean_inc(v_env_4096_);
                    leanh::lean_dec(v___x_4095_);
                    v___x_4105_ = leanh::lean_box(0);
                    v_isShared_4106_ = v_isSharedCheck_4131_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                leanh::lean_inc(v___x_3821_);
                v___x_4107_ = l_Lean_addProtected(v_env_4096_, v___x_3821_);
                if v_isShared_4106_ == 0 {
                    leanh::lean_ctor_set(v___x_4105_, 5, v___x_4079_);
                    leanh::lean_ctor_set(v___x_4105_, 0, v___x_4107_);
                    v___x_4109_ = v___x_4105_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_4130_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4130_, 0, v___x_4107_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4130_, 1, v_nextMacroScope_4097_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4130_, 2, v_ngen_4098_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4130_, 3, v_auxDeclNGen_4099_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4130_, 4, v_traceState_4100_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4130_, 5, v___x_4079_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4130_, 6, v_messages_4101_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4130_, 7, v_infoState_4102_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4130_, 8, v_snapshotTasks_4103_);
                    v___x_4109_ = v_reuseFailAlloc_4130_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_4110_ = lean_st_ref_set(v___y_3827_, v___x_4109_);
                v___x_4111_ = lean_st_ref_take(v___y_3825_);
                v_mctx_4112_ = leanh::lean_ctor_get(v___x_4111_, 0);
                v_zetaDeltaFVarIds_4113_ = leanh::lean_ctor_get(v___x_4111_, 2);
                v_postponed_4114_ = leanh::lean_ctor_get(v___x_4111_, 3);
                v_diag_4115_ = leanh::lean_ctor_get(v___x_4111_, 4);
                v_isSharedCheck_4128_ = (!leanh::lean_is_exclusive(v___x_4111_)) as u8;
                if v_isSharedCheck_4128_ == 0 {
                    v_unused_4129_ = leanh::lean_ctor_get(v___x_4111_, 1);
                    leanh::lean_dec(v_unused_4129_);
                    v___x_4117_ = v___x_4111_;
                    v_isShared_4118_ = v_isSharedCheck_4128_;
                    state = 36;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_4115_);
                    leanh::lean_inc(v_postponed_4114_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_4113_);
                    leanh::lean_inc(v_mctx_4112_);
                    leanh::lean_dec(v___x_4111_);
                    v___x_4117_ = leanh::lean_box(0);
                    v_isShared_4118_ = v_isSharedCheck_4128_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                if v_isShared_4118_ == 0 {
                    leanh::lean_ctor_set(v___x_4117_, 1, v___x_4091_);
                    v___x_4120_ = v___x_4117_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_4127_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_mctx_4112_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4127_, 1, v___x_4091_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4127_,
                        2,
                        v_zetaDeltaFVarIds_4113_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4127_, 3, v_postponed_4114_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4127_, 4, v_diag_4115_);
                    v___x_4120_ = v_reuseFailAlloc_4127_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                v___x_4121_ = lean_st_ref_set(v___y_3825_, v___x_4120_);
                v___x_4122_ = leanh::lean_unsigned_to_nat(1);
                v___x_4123_ = l_Lean_InductiveVal_numCtors(v_val_3814_);
                leanh::lean_dec_ref(v_val_3814_);
                v___x_4124_ = lean_nat_dec_eq(v___x_4123_, v___x_4122_);
                leanh::lean_dec(v___x_4123_);
                if v___x_4124_ == 0 {
                    v___y_4023_ = v___y_3824_;
                    v___y_4024_ = v___y_3825_;
                    v___y_4025_ = v___y_3826_;
                    v___y_4026_ = v___y_3827_;
                    state = 25;
                    continue;
                } else {
                    v___x_4125_ = 2;
                    leanh::lean_inc(v___x_3821_);
                    v___x_4126_ = l_Lean_Meta_setInlineAttribute(
                        v___x_3821_,
                        v___x_4125_,
                        v___y_3824_,
                        v___y_3825_,
                        v___y_3826_,
                        v___y_3827_,
                    );
                    if leanh::lean_obj_tag(v___x_4126_) == 0 {
                        leanh::lean_dec_ref_known(v___x_4126_, 1);
                        v___y_4023_ = v___y_3824_;
                        v___y_4024_ = v___y_3825_;
                        v___y_4025_ = v___y_3826_;
                        v___y_4026_ = v___y_3827_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___x_3944_);
                        leanh::lean_dec(v_a_3924_);
                        leanh::lean_dec(v_indName_3823_);
                        leanh::lean_dec(v_levelParams_3822_);
                        leanh::lean_dec(v___x_3821_);
                        leanh::lean_dec(v___x_3816_);
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
                    v_reuseFailAlloc_4147_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_a_4141_);
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
                    v_reuseFailAlloc_4155_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_a_4149_);
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
                    v_reuseFailAlloc_4163_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_a_4157_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4165_: *mut leanh::LeanObject = *_args.add(0);
    let mut v___x_4166_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_xs_4167_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___x_4168_: *mut leanh::LeanObject = *_args.add(3);
    let mut v___x_4169_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_val_4170_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___x_4171_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_4172_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___x_4173_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___x_4174_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_ctors_4175_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___x_4176_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___x_4177_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_levelParams_4178_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_indName_4179_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_4180_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_4181_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_4182_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___y_4183_: *mut leanh::LeanObject = *_args.add(18);
    let mut v___y_4184_: *mut leanh::LeanObject = *_args.add(19);
    let mut v___x_36067__boxed_4185_: u8 = 0;
    let mut v___x_36068__boxed_4186_: u8 = 0;
    let mut v_res_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_36067__boxed_4185_ = (leanh::lean_unbox(v___x_4168_) as u8);
    v___x_36068__boxed_4186_ = (leanh::lean_unbox(v___x_4169_) as u8);
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
    leanh::lean_dec(v___y_4183_);
    leanh::lean_dec_ref(v___y_4182_);
    leanh::lean_dec(v___y_4181_);
    leanh::lean_dec_ref(v___y_4180_);
    return v_res_4187_;
}
pub unsafe fn l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(
    mut v_bs_4188_: *mut leanh::LeanObject,
    mut v_k_4189_: *mut leanh::LeanObject,
    mut v___y_4190_: *mut leanh::LeanObject,
    mut v___y_4191_: *mut leanh::LeanObject,
    mut v___y_4192_: *mut leanh::LeanObject,
    mut v___y_4193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4199_: u8 = 0;
    let mut v___x_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4203_: u8 = 0;
    let mut v_a_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4207_: u8 = 0;
    let mut v___x_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4211_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4195_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(
                    leanh::lean_box(0),
                    v_bs_4188_,
                    v_k_4189_,
                    v___y_4190_,
                    v___y_4191_,
                    v___y_4192_,
                    v___y_4193_,
                );
                if leanh::lean_obj_tag(v___x_4195_) == 0 {
                    v_a_4196_ = leanh::lean_ctor_get(v___x_4195_, 0);
                    v_isSharedCheck_4203_ = (!leanh::lean_is_exclusive(v___x_4195_)) as u8;
                    if v_isSharedCheck_4203_ == 0 {
                        v___x_4198_ = v___x_4195_;
                        v_isShared_4199_ = v_isSharedCheck_4203_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4196_);
                        leanh::lean_dec(v___x_4195_);
                        v___x_4198_ = leanh::lean_box(0);
                        v_isShared_4199_ = v_isSharedCheck_4203_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4204_ = leanh::lean_ctor_get(v___x_4195_, 0);
                    v_isSharedCheck_4211_ = (!leanh::lean_is_exclusive(v___x_4195_)) as u8;
                    if v_isSharedCheck_4211_ == 0 {
                        v___x_4206_ = v___x_4195_;
                        v_isShared_4207_ = v_isSharedCheck_4211_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4204_);
                        leanh::lean_dec(v___x_4195_);
                        v___x_4206_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_4202_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4202_, 0, v_a_4196_);
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
                    v_reuseFailAlloc_4210_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4210_, 0, v_a_4204_);
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
    mut v_bs_4212_: *mut leanh::LeanObject,
    mut v_k_4213_: *mut leanh::LeanObject,
    mut v___y_4214_: *mut leanh::LeanObject,
    mut v___y_4215_: *mut leanh::LeanObject,
    mut v___y_4216_: *mut leanh::LeanObject,
    mut v___y_4217_: *mut leanh::LeanObject,
    mut v___y_4218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4219_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(v_bs_4212_, v_k_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
    leanh::lean_dec(v___y_4217_);
    leanh::lean_dec_ref(v___y_4216_);
    leanh::lean_dec(v___y_4215_);
    leanh::lean_dec_ref(v___y_4214_);
    leanh::lean_dec_ref(v_bs_4212_);
    return v_res_4219_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19(
    mut v_sz_4220_: usize,
    mut v_i_4221_: usize,
    mut v_bs_4222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4223_: u8 = 0;
    let mut v_v_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: u8 = 0;
    let mut v___x_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: usize = 0;
    let mut v___x_4232_: usize = 0;
    let mut v___x_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4223_ = lean_usize_dec_lt(v_i_4221_, v_sz_4220_);
                if v___x_4223_ == 0 {
                    return v_bs_4222_;
                } else {
                    v_v_4224_ = lean_array_uget(v_bs_4222_, v_i_4221_);
                    v___x_4225_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4226_ = lean_array_uset(v_bs_4222_, v_i_4221_, v___x_4225_);
                    v___x_4227_ = l_Lean_Expr_fvarId_x21(v_v_4224_);
                    leanh::lean_dec(v_v_4224_);
                    v___x_4228_ = 1;
                    v___x_4229_ = leanh::lean_box((v___x_4228_) as usize);
                    v___x_4230_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4230_, 0, v___x_4227_);
                    leanh::lean_ctor_set(v___x_4230_, 1, v___x_4229_);
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
    mut v_sz_4235_: *mut leanh::LeanObject,
    mut v_i_4236_: *mut leanh::LeanObject,
    mut v_bs_4237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4238_: usize = 0;
    let mut v_i_boxed_4239_: usize = 0;
    let mut v_res_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4238_ = leanh::lean_unbox_usize(v_sz_4235_);
    leanh::lean_dec(v_sz_4235_);
    v_i_boxed_4239_ = leanh::lean_unbox_usize(v_i_4236_);
    leanh::lean_dec(v_i_4236_);
    v_res_4240_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19(v_sz_boxed_4238_, v_i_boxed_4239_, v_bs_4237_);
    return v_res_4240_;
}
pub unsafe fn l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg(
    mut v_bs_4241_: *mut leanh::LeanObject,
    mut v_k_4242_: *mut leanh::LeanObject,
    mut v___y_4243_: *mut leanh::LeanObject,
    mut v___y_4244_: *mut leanh::LeanObject,
    mut v___y_4245_: *mut leanh::LeanObject,
    mut v___y_4246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_4248_: usize = 0;
    let mut v___x_4249_: usize = 0;
    let mut v___x_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_4248_ = lean_array_size(v_bs_4241_);
    v___x_4249_ = 0usize;
    v___x_4250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19(v_sz_4248_, v___x_4249_, v_bs_4241_);
    v___x_4251_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(v___x_4250_, v_k_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_);
    leanh::lean_dec_ref(v___x_4250_);
    return v___x_4251_;
}
pub unsafe fn l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg___boxed(
    mut v_bs_4252_: *mut leanh::LeanObject,
    mut v_k_4253_: *mut leanh::LeanObject,
    mut v___y_4254_: *mut leanh::LeanObject,
    mut v___y_4255_: *mut leanh::LeanObject,
    mut v___y_4256_: *mut leanh::LeanObject,
    mut v___y_4257_: *mut leanh::LeanObject,
    mut v___y_4258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4259_ = l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg(
        v_bs_4252_,
        v_k_4253_,
        v___y_4254_,
        v___y_4255_,
        v___y_4256_,
        v___y_4257_,
    );
    leanh::lean_dec(v___y_4257_);
    leanh::lean_dec_ref(v___y_4256_);
    leanh::lean_dec(v___y_4255_);
    leanh::lean_dec_ref(v___y_4254_);
    return v_res_4259_;
}
pub unsafe fn l_mkCtorIdx___lam__2(
    mut v_numParams_4263_: *mut leanh::LeanObject,
    mut v_indName_4264_: *mut leanh::LeanObject,
    mut v___x_4265_: *mut leanh::LeanObject,
    mut v___x_4266_: *mut leanh::LeanObject,
    mut v___x_4267_: u8,
    mut v___x_4268_: u8,
    mut v_val_4269_: *mut leanh::LeanObject,
    mut v___x_4270_: *mut leanh::LeanObject,
    mut v_ctors_4271_: *mut leanh::LeanObject,
    mut v___x_4272_: *mut leanh::LeanObject,
    mut v_levelParams_4273_: *mut leanh::LeanObject,
    mut v_xs_4274_: *mut leanh::LeanObject,
    mut v_x_4275_: *mut leanh::LeanObject,
    mut v___y_4276_: *mut leanh::LeanObject,
    mut v___y_4277_: *mut leanh::LeanObject,
    mut v___y_4278_: *mut leanh::LeanObject,
    mut v___y_4279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4281_ = leanh::lean_unsigned_to_nat(0);
    leanh::lean_inc(v_numParams_4263_);
    leanh::lean_inc_ref_n(v_xs_4274_, 3);
    v___x_4282_ = l_Array_toSubarray___redArg(v_xs_4274_, v___x_4281_, v_numParams_4263_);
    v___x_4283_ = l_Subarray_copy___redArg(v___x_4282_);
    v___x_4284_ = lean_array_get_size(v_xs_4274_);
    v___x_4285_ = l_Array_toSubarray___redArg(v_xs_4274_, v_numParams_4263_, v___x_4284_);
    v___x_4286_ = l_Subarray_copy___redArg(v___x_4285_);
    leanh::lean_inc(v___x_4265_);
    leanh::lean_inc(v_indName_4264_);
    v___x_4287_ = l_Lean_mkConst(v_indName_4264_, v___x_4265_);
    v___x_4288_ = l_Lean_mkAppN(v___x_4287_, v_xs_4274_);
    v___x_4289_ = l_mkCtorIdx___lam__2___closed__1;
    v___x_4290_ = l_Lean_mkConst(v___x_4289_, v___x_4266_);
    v___x_4291_ = leanh::lean_box((v___x_4267_) as usize);
    v___x_4292_ = leanh::lean_box((v___x_4268_) as usize);
    v___f_4293_ = leanh::lean_alloc_closure(
        l_mkCtorIdx___lam__1___boxed as *mut core::ffi::c_void,
        20,
        15,
    );
    leanh::lean_closure_set(v___f_4293_, 0, v___x_4288_);
    leanh::lean_closure_set(v___f_4293_, 1, v___x_4290_);
    leanh::lean_closure_set(v___f_4293_, 2, v_xs_4274_);
    leanh::lean_closure_set(v___f_4293_, 3, v___x_4291_);
    leanh::lean_closure_set(v___f_4293_, 4, v___x_4292_);
    leanh::lean_closure_set(v___f_4293_, 5, v_val_4269_);
    leanh::lean_closure_set(v___f_4293_, 6, v___x_4286_);
    leanh::lean_closure_set(v___f_4293_, 7, v___x_4265_);
    leanh::lean_closure_set(v___f_4293_, 8, v___x_4270_);
    leanh::lean_closure_set(v___f_4293_, 9, v___x_4283_);
    leanh::lean_closure_set(v___f_4293_, 10, v_ctors_4271_);
    leanh::lean_closure_set(v___f_4293_, 11, v___x_4281_);
    leanh::lean_closure_set(v___f_4293_, 12, v___x_4272_);
    leanh::lean_closure_set(v___f_4293_, 13, v_levelParams_4273_);
    leanh::lean_closure_set(v___f_4293_, 14, v_indName_4264_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_numParams_4295_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_indName_4296_: *mut leanh::LeanObject = *_args.add(1);
    let mut v___x_4297_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___x_4298_: *mut leanh::LeanObject = *_args.add(3);
    let mut v___x_4299_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___x_4300_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_val_4301_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_4302_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_ctors_4303_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___x_4304_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_levelParams_4305_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_xs_4306_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_x_4307_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_4308_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_4309_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_4310_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_4311_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_4312_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___x_36755__boxed_4313_: u8 = 0;
    let mut v___x_36756__boxed_4314_: u8 = 0;
    let mut v_res_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_36755__boxed_4313_ = (leanh::lean_unbox(v___x_4299_) as u8);
    v___x_36756__boxed_4314_ = (leanh::lean_unbox(v___x_4300_) as u8);
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
    leanh::lean_dec(v___y_4311_);
    leanh::lean_dec_ref(v___y_4310_);
    leanh::lean_dec(v___y_4309_);
    leanh::lean_dec_ref(v___y_4308_);
    leanh::lean_dec_ref(v_x_4307_);
    return v_res_4315_;
}
pub unsafe fn l_List_mapTR_loop___at___00mkCtorIdx_spec__3(
    mut v_a_4316_: *mut leanh::LeanObject,
    mut v_a_4317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4323_: u8 = 0;
    let mut v___x_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4329_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_4316_) == 0 {
                    v___x_4318_ = l_List_reverse___redArg(v_a_4317_);
                    return v___x_4318_;
                } else {
                    v_head_4319_ = leanh::lean_ctor_get(v_a_4316_, 0);
                    v_tail_4320_ = leanh::lean_ctor_get(v_a_4316_, 1);
                    v_isSharedCheck_4329_ = (!leanh::lean_is_exclusive(v_a_4316_)) as u8;
                    if v_isSharedCheck_4329_ == 0 {
                        v___x_4322_ = v_a_4316_;
                        v_isShared_4323_ = v_isSharedCheck_4329_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4320_);
                        leanh::lean_inc(v_head_4319_);
                        leanh::lean_dec(v_a_4316_);
                        v___x_4322_ = leanh::lean_box(0);
                        v_isShared_4323_ = v_isSharedCheck_4329_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4324_ = l_Lean_mkLevelParam(v_head_4319_);
                if v_isShared_4323_ == 0 {
                    leanh::lean_ctor_set(v___x_4322_, 1, v_a_4317_);
                    leanh::lean_ctor_set(v___x_4322_, 0, v___x_4324_);
                    v___x_4326_ = v___x_4322_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4328_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4328_, 0, v___x_4324_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4328_, 1, v_a_4317_);
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
pub unsafe fn _init_l_mkCtorIdx___lam__3___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4332_ = l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__6;
    v___x_4333_ = leanh::lean_unsigned_to_nat(62);
    v___x_4334_ = leanh::lean_unsigned_to_nat(48);
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
    mut v_indName_4338_: *mut leanh::LeanObject,
    mut v___x_4339_: u8,
    mut v___y_4340_: *mut leanh::LeanObject,
    mut v___y_4341_: *mut leanh::LeanObject,
    mut v___y_4342_: *mut leanh::LeanObject,
    mut v___y_4343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: u8 = 0;
    let mut v___x_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4355_: u8 = 0;
    let mut v___x_4356_: u8 = 0;
    let mut v___x_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4362_: u8 = 0;
    let mut v_toConstantVal_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4373_: u8 = 0;
    let mut v___x_4374_: u8 = 0;
    let mut v___x_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4380_: u8 = 0;
    let mut v___x_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: u8 = 0;
    let mut v___x_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4399_: u8 = 0;
    let mut v_a_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4403_: u8 = 0;
    let mut v___x_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4407_: u8 = 0;
    let mut v___x_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4412_: u8 = 0;
    let mut v_a_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4416_: u8 = 0;
    let mut v___x_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4420_: u8 = 0;
    let mut v_isSharedCheck_4421_: u8 = 0;
    let mut v___x_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4427_: u8 = 0;
    let mut v___x_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4431_: u8 = 0;
    let mut v___x_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4436_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_4345_ = leanh::lean_ctor_get(v___y_4342_, 2);
                v___x_4346_ = l___private_Lean_Meta_Constructions_CtorIdx_0__genCtorIdx;
                v___x_4347_ =
                    l_Lean_Option_get___at___00mkCtorIdx_spec__0(v_options_4345_, v___x_4346_);
                if v___x_4347_ == 0 {
                    leanh::lean_dec(v_indName_4338_);
                    v___x_4348_ = leanh::lean_box(0);
                    v___x_4349_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4349_, 0, v___x_4348_);
                    return v___x_4349_;
                } else {
                    leanh::lean_inc(v_indName_4338_);
                    v___x_4350_ = l_mkCtorIdxName(v_indName_4338_);
                    leanh::lean_inc(v___x_4350_);
                    v___x_4351_ = l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg(
                        v___x_4350_,
                        v___x_4347_,
                        v___y_4343_,
                    );
                    v_a_4352_ = leanh::lean_ctor_get(v___x_4351_, 0);
                    v_isSharedCheck_4436_ = (!leanh::lean_is_exclusive(v___x_4351_)) as u8;
                    if v_isSharedCheck_4436_ == 0 {
                        v___x_4354_ = v___x_4351_;
                        v_isShared_4355_ = v_isSharedCheck_4436_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4352_);
                        leanh::lean_dec(v___x_4351_);
                        v___x_4354_ = leanh::lean_box(0);
                        v_isShared_4355_ = v_isSharedCheck_4436_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4356_ = (leanh::lean_unbox(v_a_4352_) as u8);
                leanh::lean_dec(v_a_4352_);
                if v___x_4356_ == 0 {
                    leanh::lean_del_object(v___x_4354_);
                    leanh::lean_inc(v_indName_4338_);
                    v___x_4357_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(
                        v_indName_4338_,
                        v___y_4340_,
                        v___y_4341_,
                        v___y_4342_,
                        v___y_4343_,
                    );
                    if leanh::lean_obj_tag(v___x_4357_) == 0 {
                        v_a_4358_ = leanh::lean_ctor_get(v___x_4357_, 0);
                        leanh::lean_inc(v_a_4358_);
                        leanh::lean_dec_ref_known(v___x_4357_, 1);
                        if leanh::lean_obj_tag(v_a_4358_) == 5 {
                            v_val_4359_ = leanh::lean_ctor_get(v_a_4358_, 0);
                            v_isSharedCheck_4421_ =
                                (!leanh::lean_is_exclusive(v_a_4358_)) as u8;
                            if v_isSharedCheck_4421_ == 0 {
                                v___x_4361_ = v_a_4358_;
                                v_isShared_4362_ = v_isSharedCheck_4421_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_4359_);
                                leanh::lean_dec(v_a_4358_);
                                v___x_4361_ = leanh::lean_box(0);
                                v_isShared_4362_ = v_isSharedCheck_4421_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_4358_);
                            leanh::lean_dec(v___x_4350_);
                            leanh::lean_dec(v_indName_4338_);
                            v___x_4422_ = leanh::lean_obj_once(
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
                        leanh::lean_dec(v___x_4350_);
                        leanh::lean_dec(v_indName_4338_);
                        v_a_4424_ = leanh::lean_ctor_get(v___x_4357_, 0);
                        v_isSharedCheck_4431_ =
                            (!leanh::lean_is_exclusive(v___x_4357_)) as u8;
                        if v_isSharedCheck_4431_ == 0 {
                            v___x_4426_ = v___x_4357_;
                            v_isShared_4427_ = v_isSharedCheck_4431_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4424_);
                            leanh::lean_dec(v___x_4357_);
                            v___x_4426_ = leanh::lean_box(0);
                            v_isShared_4427_ = v_isSharedCheck_4431_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_4350_);
                    leanh::lean_dec(v_indName_4338_);
                    v___x_4432_ = leanh::lean_box(0);
                    if v_isShared_4355_ == 0 {
                        leanh::lean_ctor_set(v___x_4354_, 0, v___x_4432_);
                        v___x_4434_ = v___x_4354_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_4435_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4435_, 0, v___x_4432_);
                        v___x_4434_ = v_reuseFailAlloc_4435_;
                        state = 14;
                        continue;
                    }
                }
            }
            2 => {
                v_toConstantVal_4363_ = leanh::lean_ctor_get(v_val_4359_, 0);
                v_numParams_4364_ = leanh::lean_ctor_get(v_val_4359_, 1);
                leanh::lean_inc(v_numParams_4364_);
                v_numIndices_4365_ = leanh::lean_ctor_get(v_val_4359_, 2);
                leanh::lean_inc(v_numIndices_4365_);
                v_ctors_4366_ = leanh::lean_ctor_get(v_val_4359_, 4);
                leanh::lean_inc(v_ctors_4366_);
                v_levelParams_4367_ = leanh::lean_ctor_get(v_toConstantVal_4363_, 1);
                leanh::lean_inc(v_levelParams_4367_);
                v_type_4368_ = leanh::lean_ctor_get(v_toConstantVal_4363_, 2);
                leanh::lean_inc_ref_n(v_type_4368_, 2);
                v___x_4369_ = l_Lean_Meta_isPropFormerType(
                    v_type_4368_,
                    v___y_4340_,
                    v___y_4341_,
                    v___y_4342_,
                    v___y_4343_,
                );
                if leanh::lean_obj_tag(v___x_4369_) == 0 {
                    v_a_4370_ = leanh::lean_ctor_get(v___x_4369_, 0);
                    v_isSharedCheck_4412_ = (!leanh::lean_is_exclusive(v___x_4369_)) as u8;
                    if v_isSharedCheck_4412_ == 0 {
                        v___x_4372_ = v___x_4369_;
                        v_isShared_4373_ = v_isSharedCheck_4412_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4370_);
                        leanh::lean_dec(v___x_4369_);
                        v___x_4372_ = leanh::lean_box(0);
                        v_isShared_4373_ = v_isSharedCheck_4412_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_type_4368_);
                    leanh::lean_dec(v_levelParams_4367_);
                    leanh::lean_dec(v_ctors_4366_);
                    leanh::lean_dec(v_numIndices_4365_);
                    leanh::lean_dec(v_numParams_4364_);
                    leanh::lean_del_object(v___x_4361_);
                    leanh::lean_dec_ref(v_val_4359_);
                    leanh::lean_dec(v___x_4350_);
                    leanh::lean_dec(v_indName_4338_);
                    v_a_4413_ = leanh::lean_ctor_get(v___x_4369_, 0);
                    v_isSharedCheck_4420_ = (!leanh::lean_is_exclusive(v___x_4369_)) as u8;
                    if v_isSharedCheck_4420_ == 0 {
                        v___x_4415_ = v___x_4369_;
                        v_isShared_4416_ = v_isSharedCheck_4420_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4413_);
                        leanh::lean_dec(v___x_4369_);
                        v___x_4415_ = leanh::lean_box(0);
                        v_isShared_4416_ = v_isSharedCheck_4420_;
                        state = 10;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4374_ = (leanh::lean_unbox(v_a_4370_) as u8);
                leanh::lean_dec(v_a_4370_);
                if v___x_4374_ == 0 {
                    leanh::lean_del_object(v___x_4372_);
                    leanh::lean_inc(v_indName_4338_);
                    v___x_4375_ = l_Lean_mkCasesOnName(v_indName_4338_);
                    leanh::lean_inc(v___x_4375_);
                    v___x_4376_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(
                        v___x_4375_,
                        v___y_4340_,
                        v___y_4341_,
                        v___y_4342_,
                        v___y_4343_,
                    );
                    if leanh::lean_obj_tag(v___x_4376_) == 0 {
                        v_a_4377_ = leanh::lean_ctor_get(v___x_4376_, 0);
                        v_isSharedCheck_4399_ =
                            (!leanh::lean_is_exclusive(v___x_4376_)) as u8;
                        if v_isSharedCheck_4399_ == 0 {
                            v___x_4379_ = v___x_4376_;
                            v_isShared_4380_ = v_isSharedCheck_4399_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4377_);
                            leanh::lean_dec(v___x_4376_);
                            v___x_4379_ = leanh::lean_box(0);
                            v_isShared_4380_ = v_isSharedCheck_4399_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_4375_);
                        leanh::lean_dec_ref(v_type_4368_);
                        leanh::lean_dec(v_levelParams_4367_);
                        leanh::lean_dec(v_ctors_4366_);
                        leanh::lean_dec(v_numIndices_4365_);
                        leanh::lean_dec(v_numParams_4364_);
                        leanh::lean_del_object(v___x_4361_);
                        leanh::lean_dec_ref(v_val_4359_);
                        leanh::lean_dec(v___x_4350_);
                        leanh::lean_dec(v_indName_4338_);
                        v_a_4400_ = leanh::lean_ctor_get(v___x_4376_, 0);
                        v_isSharedCheck_4407_ =
                            (!leanh::lean_is_exclusive(v___x_4376_)) as u8;
                        if v_isSharedCheck_4407_ == 0 {
                            v___x_4402_ = v___x_4376_;
                            v_isShared_4403_ = v_isSharedCheck_4407_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4400_);
                            leanh::lean_dec(v___x_4376_);
                            v___x_4402_ = leanh::lean_box(0);
                            v_isShared_4403_ = v_isSharedCheck_4407_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_type_4368_);
                    leanh::lean_dec(v_levelParams_4367_);
                    leanh::lean_dec(v_ctors_4366_);
                    leanh::lean_dec(v_numIndices_4365_);
                    leanh::lean_dec(v_numParams_4364_);
                    leanh::lean_del_object(v___x_4361_);
                    leanh::lean_dec_ref(v_val_4359_);
                    leanh::lean_dec(v___x_4350_);
                    leanh::lean_dec(v_indName_4338_);
                    v___x_4408_ = leanh::lean_box(0);
                    if v_isShared_4373_ == 0 {
                        leanh::lean_ctor_set(v___x_4372_, 0, v___x_4408_);
                        v___x_4410_ = v___x_4372_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4411_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4411_, 0, v___x_4408_);
                        v___x_4410_ = v_reuseFailAlloc_4411_;
                        state = 9;
                        continue;
                    }
                }
            }
            4 => {
                v___x_4381_ = l_List_lengthTR___redArg(v_levelParams_4367_);
                v___x_4382_ = l_Lean_ConstantInfo_levelParams(v_a_4377_);
                leanh::lean_dec(v_a_4377_);
                v___x_4383_ = l_List_lengthTR___redArg(v___x_4382_);
                leanh::lean_dec(v___x_4382_);
                v___x_4384_ = lean_nat_dec_lt(v___x_4381_, v___x_4383_);
                leanh::lean_dec(v___x_4383_);
                leanh::lean_dec(v___x_4381_);
                if v___x_4384_ == 0 {
                    leanh::lean_dec(v___x_4375_);
                    leanh::lean_dec_ref(v_type_4368_);
                    leanh::lean_dec(v_levelParams_4367_);
                    leanh::lean_dec(v_ctors_4366_);
                    leanh::lean_dec(v_numIndices_4365_);
                    leanh::lean_dec(v_numParams_4364_);
                    leanh::lean_del_object(v___x_4361_);
                    leanh::lean_dec_ref(v_val_4359_);
                    leanh::lean_dec(v___x_4350_);
                    leanh::lean_dec(v_indName_4338_);
                    v___x_4385_ = leanh::lean_box(0);
                    if v_isShared_4380_ == 0 {
                        leanh::lean_ctor_set(v___x_4379_, 0, v___x_4385_);
                        v___x_4387_ = v___x_4379_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4388_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4388_, 0, v___x_4385_);
                        v___x_4387_ = v_reuseFailAlloc_4388_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4379_);
                    v___x_4389_ = leanh::lean_box(0);
                    leanh::lean_inc(v_levelParams_4367_);
                    v___x_4390_ = l_List_mapTR_loop___at___00mkCtorIdx_spec__3(
                        v_levelParams_4367_,
                        v___x_4389_,
                    );
                    v___x_4391_ = leanh::lean_box((v___x_4339_) as usize);
                    v___x_4392_ = leanh::lean_box((v___x_4347_) as usize);
                    leanh::lean_inc(v_numParams_4364_);
                    v___f_4393_ = leanh::lean_alloc_closure(
                        l_mkCtorIdx___lam__2___boxed as *mut core::ffi::c_void,
                        18,
                        11,
                    );
                    leanh::lean_closure_set(v___f_4393_, 0, v_numParams_4364_);
                    leanh::lean_closure_set(v___f_4393_, 1, v_indName_4338_);
                    leanh::lean_closure_set(v___f_4393_, 2, v___x_4390_);
                    leanh::lean_closure_set(v___f_4393_, 3, v___x_4389_);
                    leanh::lean_closure_set(v___f_4393_, 4, v___x_4391_);
                    leanh::lean_closure_set(v___f_4393_, 5, v___x_4392_);
                    leanh::lean_closure_set(v___f_4393_, 6, v_val_4359_);
                    leanh::lean_closure_set(v___f_4393_, 7, v___x_4375_);
                    leanh::lean_closure_set(v___f_4393_, 8, v_ctors_4366_);
                    leanh::lean_closure_set(v___f_4393_, 9, v___x_4350_);
                    leanh::lean_closure_set(v___f_4393_, 10, v_levelParams_4367_);
                    v___x_4394_ = lean_nat_add(v_numParams_4364_, v_numIndices_4365_);
                    leanh::lean_dec(v_numIndices_4365_);
                    leanh::lean_dec(v_numParams_4364_);
                    if v_isShared_4362_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4361_, 1);
                        leanh::lean_ctor_set(v___x_4361_, 0, v___x_4394_);
                        v___x_4396_ = v___x_4361_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4398_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4398_, 0, v___x_4394_);
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
                    v_reuseFailAlloc_4406_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4406_, 0, v_a_4400_);
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
                    v_reuseFailAlloc_4419_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_a_4413_);
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
                    v_reuseFailAlloc_4430_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4430_, 0, v_a_4424_);
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
    mut v_indName_4437_: *mut leanh::LeanObject,
    mut v___x_4438_: *mut leanh::LeanObject,
    mut v___y_4439_: *mut leanh::LeanObject,
    mut v___y_4440_: *mut leanh::LeanObject,
    mut v___y_4441_: *mut leanh::LeanObject,
    mut v___y_4442_: *mut leanh::LeanObject,
    mut v___y_4443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_36868__boxed_4444_: u8 = 0;
    let mut v_res_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_36868__boxed_4444_ = (leanh::lean_unbox(v___x_4438_) as u8);
    v_res_4445_ = l_mkCtorIdx___lam__3(
        v_indName_4437_,
        v___x_36868__boxed_4444_,
        v___y_4439_,
        v___y_4440_,
        v___y_4441_,
        v___y_4442_,
    );
    leanh::lean_dec(v___y_4442_);
    leanh::lean_dec_ref(v___y_4441_);
    leanh::lean_dec(v___y_4440_);
    leanh::lean_dec_ref(v___y_4439_);
    return v_res_4445_;
}
pub unsafe fn l_mkCtorIdx___lam__4(
    mut v___x_4446_: *mut leanh::LeanObject,
    mut v_e_4447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4448_ = l_Lean_indentD(v_e_4447_);
    v___x_4449_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4449_, 0, v___x_4446_);
    leanh::lean_ctor_set(v___x_4449_, 1, v___x_4448_);
    return v___x_4449_;
}
pub unsafe fn l_mkCtorIdx___lam__5(
    mut v___f_4450_: *mut leanh::LeanObject,
    mut v___f_4451_: *mut leanh::LeanObject,
    mut v___y_4452_: *mut leanh::LeanObject,
    mut v___y_4453_: *mut leanh::LeanObject,
    mut v___y_4454_: *mut leanh::LeanObject,
    mut v___y_4455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4461_: u8 = 0;
    let mut v___x_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4465_: u8 = 0;
    let mut v_a_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4469_: u8 = 0;
    let mut v___x_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_4457_) == 0 {
                    v_a_4458_ = leanh::lean_ctor_get(v___x_4457_, 0);
                    v_isSharedCheck_4465_ = (!leanh::lean_is_exclusive(v___x_4457_)) as u8;
                    if v_isSharedCheck_4465_ == 0 {
                        v___x_4460_ = v___x_4457_;
                        v_isShared_4461_ = v_isSharedCheck_4465_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4458_);
                        leanh::lean_dec(v___x_4457_);
                        v___x_4460_ = leanh::lean_box(0);
                        v_isShared_4461_ = v_isSharedCheck_4465_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4466_ = leanh::lean_ctor_get(v___x_4457_, 0);
                    v_isSharedCheck_4473_ = (!leanh::lean_is_exclusive(v___x_4457_)) as u8;
                    if v_isSharedCheck_4473_ == 0 {
                        v___x_4468_ = v___x_4457_;
                        v_isShared_4469_ = v_isSharedCheck_4473_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4466_);
                        leanh::lean_dec(v___x_4457_);
                        v___x_4468_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_4464_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4464_, 0, v_a_4458_);
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
                    v_reuseFailAlloc_4472_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4472_, 0, v_a_4466_);
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
    mut v___f_4474_: *mut leanh::LeanObject,
    mut v___f_4475_: *mut leanh::LeanObject,
    mut v___y_4476_: *mut leanh::LeanObject,
    mut v___y_4477_: *mut leanh::LeanObject,
    mut v___y_4478_: *mut leanh::LeanObject,
    mut v___y_4479_: *mut leanh::LeanObject,
    mut v___y_4480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4481_ = l_mkCtorIdx___lam__5(
        v___f_4474_,
        v___f_4475_,
        v___y_4476_,
        v___y_4477_,
        v___y_4478_,
        v___y_4479_,
    );
    leanh::lean_dec(v___y_4479_);
    leanh::lean_dec_ref(v___y_4478_);
    leanh::lean_dec(v___y_4477_);
    leanh::lean_dec_ref(v___y_4476_);
    return v_res_4481_;
}
pub unsafe fn _init_l_mkCtorIdx___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4483_ = l_mkCtorIdx___closed__0;
    v___x_4484_ = l_Lean_stringToMessageData(v___x_4483_);
    return v___x_4484_;
}
pub unsafe fn _init_l_mkCtorIdx___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4486_ = l_mkCtorIdx___closed__2;
    v___x_4487_ = l_Lean_stringToMessageData(v___x_4486_);
    return v___x_4487_;
}
pub unsafe fn l_mkCtorIdx(
    mut v_indName_4488_: *mut leanh::LeanObject,
    mut v_a_4489_: *mut leanh::LeanObject,
    mut v_a_4490_: *mut leanh::LeanObject,
    mut v_a_4491_: *mut leanh::LeanObject,
    mut v_a_4492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: u8 = 0;
    let mut v___x_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: u8 = 0;
    v___x_4494_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_mkCtorIdx___closed__1),
        core::ptr::addr_of_mut!(l_mkCtorIdx___closed__1_once),
        _init_l_mkCtorIdx___closed__1,
    );
    v___x_4495_ = 0;
    v___x_4496_ = leanh::lean_box((v___x_4495_) as usize);
    leanh::lean_inc_n(v_indName_4488_, 2);
    v___f_4497_ = leanh::lean_alloc_closure(
        l_mkCtorIdx___lam__3___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___f_4497_, 0, v_indName_4488_);
    leanh::lean_closure_set(v___f_4497_, 1, v___x_4496_);
    v___x_4498_ = l_Lean_MessageData_ofConstName(v_indName_4488_, v___x_4495_);
    v___x_4499_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4499_, 0, v___x_4494_);
    leanh::lean_ctor_set(v___x_4499_, 1, v___x_4498_);
    v___x_4500_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_mkCtorIdx___closed__3),
        core::ptr::addr_of_mut!(l_mkCtorIdx___closed__3_once),
        _init_l_mkCtorIdx___closed__3,
    );
    v___x_4501_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4501_, 0, v___x_4499_);
    leanh::lean_ctor_set(v___x_4501_, 1, v___x_4500_);
    v___f_4502_ =
        leanh::lean_alloc_closure(l_mkCtorIdx___lam__4 as *mut core::ffi::c_void, 2, 1);
    leanh::lean_closure_set(v___f_4502_, 0, v___x_4501_);
    v___f_4503_ = leanh::lean_alloc_closure(
        l_mkCtorIdx___lam__5___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___f_4503_, 0, v___f_4497_);
    leanh::lean_closure_set(v___f_4503_, 1, v___f_4502_);
    v___x_4504_ = l_Lean_isPrivateName(v_indName_4488_);
    leanh::lean_dec(v_indName_4488_);
    if v___x_4504_ == 0 {
        let mut v___x_4505_: u8 = 0;
        let mut v___x_4506_: *mut leanh::LeanObject = core::ptr::null_mut();
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
        let mut v___x_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_indName_4508_: *mut leanh::LeanObject,
    mut v_a_4509_: *mut leanh::LeanObject,
    mut v_a_4510_: *mut leanh::LeanObject,
    mut v_a_4511_: *mut leanh::LeanObject,
    mut v_a_4512_: *mut leanh::LeanObject,
    mut v_a_4513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4514_ = l_mkCtorIdx(v_indName_4508_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_);
    leanh::lean_dec(v_a_4512_);
    leanh::lean_dec_ref(v_a_4511_);
    leanh::lean_dec(v_a_4510_);
    leanh::lean_dec_ref(v_a_4509_);
    return v_res_4514_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6(
    mut v___x_4515_: u8,
    mut v___x_4516_: *mut leanh::LeanObject,
    mut v_as_4517_: *mut leanh::LeanObject,
    mut v_as_x27_4518_: *mut leanh::LeanObject,
    mut v_b_4519_: *mut leanh::LeanObject,
    mut v_a_4520_: *mut leanh::LeanObject,
    mut v___y_4521_: *mut leanh::LeanObject,
    mut v___y_4522_: *mut leanh::LeanObject,
    mut v___y_4523_: *mut leanh::LeanObject,
    mut v___y_4524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v___x_4527_: *mut leanh::LeanObject,
    mut v___x_4528_: *mut leanh::LeanObject,
    mut v_as_4529_: *mut leanh::LeanObject,
    mut v_as_x27_4530_: *mut leanh::LeanObject,
    mut v_b_4531_: *mut leanh::LeanObject,
    mut v_a_4532_: *mut leanh::LeanObject,
    mut v___y_4533_: *mut leanh::LeanObject,
    mut v___y_4534_: *mut leanh::LeanObject,
    mut v___y_4535_: *mut leanh::LeanObject,
    mut v___y_4536_: *mut leanh::LeanObject,
    mut v___y_4537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_37175__boxed_4538_: u8 = 0;
    let mut v_res_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_37175__boxed_4538_ = (leanh::lean_unbox(v___x_4527_) as u8);
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
    leanh::lean_dec(v___y_4536_);
    leanh::lean_dec_ref(v___y_4535_);
    leanh::lean_dec(v___y_4534_);
    leanh::lean_dec_ref(v___y_4533_);
    leanh::lean_dec(v_as_x27_4530_);
    leanh::lean_dec(v_as_4529_);
    leanh::lean_dec_ref(v___x_4528_);
    return v_res_4539_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10(
    mut v_00_u03b1_4540_: *mut leanh::LeanObject,
    mut v_name_4541_: *mut leanh::LeanObject,
    mut v_bi_4542_: u8,
    mut v_type_4543_: *mut leanh::LeanObject,
    mut v_k_4544_: *mut leanh::LeanObject,
    mut v_kind_4545_: u8,
    mut v___y_4546_: *mut leanh::LeanObject,
    mut v___y_4547_: *mut leanh::LeanObject,
    mut v___y_4548_: *mut leanh::LeanObject,
    mut v___y_4549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4551_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(v_name_4541_, v_bi_4542_, v_type_4543_, v_k_4544_, v_kind_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_);
    return v___x_4551_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___boxed(
    mut v_00_u03b1_4552_: *mut leanh::LeanObject,
    mut v_name_4553_: *mut leanh::LeanObject,
    mut v_bi_4554_: *mut leanh::LeanObject,
    mut v_type_4555_: *mut leanh::LeanObject,
    mut v_k_4556_: *mut leanh::LeanObject,
    mut v_kind_4557_: *mut leanh::LeanObject,
    mut v___y_4558_: *mut leanh::LeanObject,
    mut v___y_4559_: *mut leanh::LeanObject,
    mut v___y_4560_: *mut leanh::LeanObject,
    mut v___y_4561_: *mut leanh::LeanObject,
    mut v___y_4562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_4563_: u8 = 0;
    let mut v_kind_boxed_4564_: u8 = 0;
    let mut v_res_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_4563_ = (leanh::lean_unbox(v_bi_4554_) as u8);
    v_kind_boxed_4564_ = (leanh::lean_unbox(v_kind_4557_) as u8);
    v_res_4565_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10(v_00_u03b1_4552_, v_name_4553_, v_bi_boxed_4563_, v_type_4555_, v_k_4556_, v_kind_boxed_4564_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_);
    leanh::lean_dec(v___y_4561_);
    leanh::lean_dec_ref(v___y_4560_);
    leanh::lean_dec(v___y_4559_);
    leanh::lean_dec_ref(v___y_4558_);
    return v_res_4565_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7(
    mut v_00_u03b1_4566_: *mut leanh::LeanObject,
    mut v_name_4567_: *mut leanh::LeanObject,
    mut v_type_4568_: *mut leanh::LeanObject,
    mut v_k_4569_: *mut leanh::LeanObject,
    mut v___y_4570_: *mut leanh::LeanObject,
    mut v___y_4571_: *mut leanh::LeanObject,
    mut v___y_4572_: *mut leanh::LeanObject,
    mut v___y_4573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4576_: *mut leanh::LeanObject,
    mut v_name_4577_: *mut leanh::LeanObject,
    mut v_type_4578_: *mut leanh::LeanObject,
    mut v_k_4579_: *mut leanh::LeanObject,
    mut v___y_4580_: *mut leanh::LeanObject,
    mut v___y_4581_: *mut leanh::LeanObject,
    mut v___y_4582_: *mut leanh::LeanObject,
    mut v___y_4583_: *mut leanh::LeanObject,
    mut v___y_4584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4585_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_4583_);
    leanh::lean_dec_ref(v___y_4582_);
    leanh::lean_dec(v___y_4581_);
    leanh::lean_dec_ref(v___y_4580_);
    return v_res_4585_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15(
    mut v_declName_4586_: *mut leanh::LeanObject,
    mut v_s_4587_: u8,
    mut v___y_4588_: *mut leanh::LeanObject,
    mut v___y_4589_: *mut leanh::LeanObject,
    mut v___y_4590_: *mut leanh::LeanObject,
    mut v___y_4591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4593_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(v_declName_4586_, v_s_4587_, v___y_4589_, v___y_4591_);
    return v___x_4593_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___boxed(
    mut v_declName_4594_: *mut leanh::LeanObject,
    mut v_s_4595_: *mut leanh::LeanObject,
    mut v___y_4596_: *mut leanh::LeanObject,
    mut v___y_4597_: *mut leanh::LeanObject,
    mut v___y_4598_: *mut leanh::LeanObject,
    mut v___y_4599_: *mut leanh::LeanObject,
    mut v___y_4600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_boxed_4601_: u8 = 0;
    let mut v_res_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_s_boxed_4601_ = (leanh::lean_unbox(v_s_4595_) as u8);
    v_res_4602_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15(v_declName_4594_, v_s_boxed_4601_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_);
    leanh::lean_dec(v___y_4599_);
    leanh::lean_dec_ref(v___y_4598_);
    leanh::lean_dec(v___y_4597_);
    leanh::lean_dec_ref(v___y_4596_);
    return v_res_4602_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17(
    mut v_env_4603_: *mut leanh::LeanObject,
    mut v___y_4604_: *mut leanh::LeanObject,
    mut v___y_4605_: *mut leanh::LeanObject,
    mut v___y_4606_: *mut leanh::LeanObject,
    mut v___y_4607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4609_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(v_env_4603_, v___y_4605_, v___y_4607_);
    return v___x_4609_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___boxed(
    mut v_env_4610_: *mut leanh::LeanObject,
    mut v___y_4611_: *mut leanh::LeanObject,
    mut v___y_4612_: *mut leanh::LeanObject,
    mut v___y_4613_: *mut leanh::LeanObject,
    mut v___y_4614_: *mut leanh::LeanObject,
    mut v___y_4615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4616_ =
        l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17(
            v_env_4610_,
            v___y_4611_,
            v___y_4612_,
            v___y_4613_,
            v___y_4614_,
        );
    leanh::lean_dec(v___y_4614_);
    leanh::lean_dec_ref(v___y_4613_);
    leanh::lean_dec(v___y_4612_);
    leanh::lean_dec_ref(v___y_4611_);
    return v_res_4616_;
}
pub unsafe fn l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20(
    mut v_00_u03b1_4617_: *mut leanh::LeanObject,
    mut v_bs_4618_: *mut leanh::LeanObject,
    mut v_k_4619_: *mut leanh::LeanObject,
    mut v___y_4620_: *mut leanh::LeanObject,
    mut v___y_4621_: *mut leanh::LeanObject,
    mut v___y_4622_: *mut leanh::LeanObject,
    mut v___y_4623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4625_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(v_bs_4618_, v_k_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_);
    return v___x_4625_;
}
pub unsafe fn l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___boxed(
    mut v_00_u03b1_4626_: *mut leanh::LeanObject,
    mut v_bs_4627_: *mut leanh::LeanObject,
    mut v_k_4628_: *mut leanh::LeanObject,
    mut v___y_4629_: *mut leanh::LeanObject,
    mut v___y_4630_: *mut leanh::LeanObject,
    mut v___y_4631_: *mut leanh::LeanObject,
    mut v___y_4632_: *mut leanh::LeanObject,
    mut v___y_4633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4634_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20(v_00_u03b1_4626_, v_bs_4627_, v_k_4628_, v___y_4629_, v___y_4630_, v___y_4631_, v___y_4632_);
    leanh::lean_dec(v___y_4632_);
    leanh::lean_dec_ref(v___y_4631_);
    leanh::lean_dec(v___y_4630_);
    leanh::lean_dec_ref(v___y_4629_);
    leanh::lean_dec_ref(v_bs_4627_);
    return v_res_4634_;
}
pub unsafe fn l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12(
    mut v_00_u03b1_4635_: *mut leanh::LeanObject,
    mut v_bs_4636_: *mut leanh::LeanObject,
    mut v_k_4637_: *mut leanh::LeanObject,
    mut v___y_4638_: *mut leanh::LeanObject,
    mut v___y_4639_: *mut leanh::LeanObject,
    mut v___y_4640_: *mut leanh::LeanObject,
    mut v___y_4641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4644_: *mut leanh::LeanObject,
    mut v_bs_4645_: *mut leanh::LeanObject,
    mut v_k_4646_: *mut leanh::LeanObject,
    mut v___y_4647_: *mut leanh::LeanObject,
    mut v___y_4648_: *mut leanh::LeanObject,
    mut v___y_4649_: *mut leanh::LeanObject,
    mut v___y_4650_: *mut leanh::LeanObject,
    mut v___y_4651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4652_ = l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12(
        v_00_u03b1_4644_,
        v_bs_4645_,
        v_k_4646_,
        v___y_4647_,
        v___y_4648_,
        v___y_4649_,
        v___y_4650_,
    );
    leanh::lean_dec(v___y_4650_);
    leanh::lean_dec_ref(v___y_4649_);
    leanh::lean_dec(v___y_4648_);
    leanh::lean_dec_ref(v___y_4647_);
    return v_res_4652_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2(
    mut v_00_u03b1_4653_: *mut leanh::LeanObject,
    mut v_constName_4654_: *mut leanh::LeanObject,
    mut v___y_4655_: *mut leanh::LeanObject,
    mut v___y_4656_: *mut leanh::LeanObject,
    mut v___y_4657_: *mut leanh::LeanObject,
    mut v___y_4658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4660_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(v_constName_4654_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_);
    return v___x_4660_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___boxed(
    mut v_00_u03b1_4661_: *mut leanh::LeanObject,
    mut v_constName_4662_: *mut leanh::LeanObject,
    mut v___y_4663_: *mut leanh::LeanObject,
    mut v___y_4664_: *mut leanh::LeanObject,
    mut v___y_4665_: *mut leanh::LeanObject,
    mut v___y_4666_: *mut leanh::LeanObject,
    mut v___y_4667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4668_ =
        l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2(
            v_00_u03b1_4661_,
            v_constName_4662_,
            v___y_4663_,
            v___y_4664_,
            v___y_4665_,
            v___y_4666_,
        );
    leanh::lean_dec(v___y_4666_);
    leanh::lean_dec_ref(v___y_4665_);
    leanh::lean_dec(v___y_4664_);
    leanh::lean_dec_ref(v___y_4663_);
    return v_res_4668_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5(
    mut v_00_u03b1_4669_: *mut leanh::LeanObject,
    mut v_msg_4670_: *mut leanh::LeanObject,
    mut v___y_4671_: *mut leanh::LeanObject,
    mut v___y_4672_: *mut leanh::LeanObject,
    mut v___y_4673_: *mut leanh::LeanObject,
    mut v___y_4674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4676_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v_msg_4670_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_);
    return v___x_4676_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___boxed(
    mut v_00_u03b1_4677_: *mut leanh::LeanObject,
    mut v_msg_4678_: *mut leanh::LeanObject,
    mut v___y_4679_: *mut leanh::LeanObject,
    mut v___y_4680_: *mut leanh::LeanObject,
    mut v___y_4681_: *mut leanh::LeanObject,
    mut v___y_4682_: *mut leanh::LeanObject,
    mut v___y_4683_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4684_ =
        l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5(
            v_00_u03b1_4677_,
            v_msg_4678_,
            v___y_4679_,
            v___y_4680_,
            v___y_4681_,
            v___y_4682_,
        );
    leanh::lean_dec(v___y_4682_);
    leanh::lean_dec_ref(v___y_4681_);
    leanh::lean_dec(v___y_4680_);
    leanh::lean_dec_ref(v___y_4679_);
    return v_res_4684_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7(
    mut v_00_u03b1_4685_: *mut leanh::LeanObject,
    mut v_ref_4686_: *mut leanh::LeanObject,
    mut v_constName_4687_: *mut leanh::LeanObject,
    mut v___y_4688_: *mut leanh::LeanObject,
    mut v___y_4689_: *mut leanh::LeanObject,
    mut v___y_4690_: *mut leanh::LeanObject,
    mut v___y_4691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4693_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_4686_, v_constName_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_);
    return v___x_4693_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___boxed(
    mut v_00_u03b1_4694_: *mut leanh::LeanObject,
    mut v_ref_4695_: *mut leanh::LeanObject,
    mut v_constName_4696_: *mut leanh::LeanObject,
    mut v___y_4697_: *mut leanh::LeanObject,
    mut v___y_4698_: *mut leanh::LeanObject,
    mut v___y_4699_: *mut leanh::LeanObject,
    mut v___y_4700_: *mut leanh::LeanObject,
    mut v___y_4701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4702_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7(v_00_u03b1_4694_, v_ref_4695_, v_constName_4696_, v___y_4697_, v___y_4698_, v___y_4699_, v___y_4700_);
    leanh::lean_dec(v___y_4700_);
    leanh::lean_dec_ref(v___y_4699_);
    leanh::lean_dec(v___y_4698_);
    leanh::lean_dec_ref(v___y_4697_);
    leanh::lean_dec(v_ref_4695_);
    return v_res_4702_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21(
    mut v_00_u03b1_4703_: *mut leanh::LeanObject,
    mut v_ref_4704_: *mut leanh::LeanObject,
    mut v_msg_4705_: *mut leanh::LeanObject,
    mut v_declHint_4706_: *mut leanh::LeanObject,
    mut v___y_4707_: *mut leanh::LeanObject,
    mut v___y_4708_: *mut leanh::LeanObject,
    mut v___y_4709_: *mut leanh::LeanObject,
    mut v___y_4710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4712_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(v_ref_4704_, v_msg_4705_, v_declHint_4706_, v___y_4707_, v___y_4708_, v___y_4709_, v___y_4710_);
    return v___x_4712_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___boxed(
    mut v_00_u03b1_4713_: *mut leanh::LeanObject,
    mut v_ref_4714_: *mut leanh::LeanObject,
    mut v_msg_4715_: *mut leanh::LeanObject,
    mut v_declHint_4716_: *mut leanh::LeanObject,
    mut v___y_4717_: *mut leanh::LeanObject,
    mut v___y_4718_: *mut leanh::LeanObject,
    mut v___y_4719_: *mut leanh::LeanObject,
    mut v___y_4720_: *mut leanh::LeanObject,
    mut v___y_4721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4722_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21(v_00_u03b1_4713_, v_ref_4714_, v_msg_4715_, v_declHint_4716_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
    leanh::lean_dec(v___y_4720_);
    leanh::lean_dec_ref(v___y_4719_);
    leanh::lean_dec(v___y_4718_);
    leanh::lean_dec_ref(v___y_4717_);
    leanh::lean_dec(v_ref_4714_);
    return v_res_4722_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27(
    mut v_msg_4723_: *mut leanh::LeanObject,
    mut v_declHint_4724_: *mut leanh::LeanObject,
    mut v___y_4725_: *mut leanh::LeanObject,
    mut v___y_4726_: *mut leanh::LeanObject,
    mut v___y_4727_: *mut leanh::LeanObject,
    mut v___y_4728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4730_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(v_msg_4723_, v_declHint_4724_, v___y_4728_);
    return v___x_4730_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___boxed(
    mut v_msg_4731_: *mut leanh::LeanObject,
    mut v_declHint_4732_: *mut leanh::LeanObject,
    mut v___y_4733_: *mut leanh::LeanObject,
    mut v___y_4734_: *mut leanh::LeanObject,
    mut v___y_4735_: *mut leanh::LeanObject,
    mut v___y_4736_: *mut leanh::LeanObject,
    mut v___y_4737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4738_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27(v_msg_4731_, v_declHint_4732_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_);
    leanh::lean_dec(v___y_4736_);
    leanh::lean_dec_ref(v___y_4735_);
    leanh::lean_dec(v___y_4734_);
    leanh::lean_dec_ref(v___y_4733_);
    return v_res_4738_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27(
    mut v_00_u03b1_4739_: *mut leanh::LeanObject,
    mut v_ref_4740_: *mut leanh::LeanObject,
    mut v_msg_4741_: *mut leanh::LeanObject,
    mut v___y_4742_: *mut leanh::LeanObject,
    mut v___y_4743_: *mut leanh::LeanObject,
    mut v___y_4744_: *mut leanh::LeanObject,
    mut v___y_4745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4747_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(v_ref_4740_, v_msg_4741_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_);
    return v___x_4747_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___boxed(
    mut v_00_u03b1_4748_: *mut leanh::LeanObject,
    mut v_ref_4749_: *mut leanh::LeanObject,
    mut v_msg_4750_: *mut leanh::LeanObject,
    mut v___y_4751_: *mut leanh::LeanObject,
    mut v___y_4752_: *mut leanh::LeanObject,
    mut v___y_4753_: *mut leanh::LeanObject,
    mut v___y_4754_: *mut leanh::LeanObject,
    mut v___y_4755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4756_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27(v_00_u03b1_4748_, v_ref_4749_, v_msg_4750_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_);
    leanh::lean_dec(v___y_4754_);
    leanh::lean_dec_ref(v___y_4753_);
    leanh::lean_dec(v___y_4752_);
    leanh::lean_dec_ref(v___y_4751_);
    leanh::lean_dec(v_ref_4749_);
    return v_res_4756_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Constructions_CtorIdx(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_AddDecl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CompletionName(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Deprecated(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Constructions_CtorIdx_0__initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_Meta_Constructions_CtorIdx_0__genCtorIdx =
        leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l___private_Lean_Meta_Constructions_CtorIdx_0__genCtorIdx);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Constructions_CtorIdx(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Constructions_CtorIdx(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_AddDecl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_CompletionName(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Linter_Deprecated(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Constructions_CtorIdx(builtin);
}