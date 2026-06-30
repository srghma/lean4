// Lean compiler output
// Module: Lean.Meta.Constructions.CtorElim
// Imports: Lean.Meta.Basic Lean.Meta.CompletionName Lean.Meta.Constructions.CtorIdx Lean.Meta.NatTable Lean.Elab.App
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed, lean_array_get_size,
    lean_array_mk, lean_array_pop, lean_array_push, lean_array_size, lean_array_uget_borrowed,
    lean_array_uset, lean_infer_type, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_st_mk_ref,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_usize_add, lean_usize_dec_eq,
    lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub, lean_whnf,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Array::Subarray::{
    l_Array_toSubarray___redArg, l_Subarray_get___redArg,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::GetElem::{l_List_get_x21Internal___redArg, l_outOfBounds___redArg};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_appendCore, l_Lean_Name_str___override, l_Lean_replaceRef, l_List_lengthTR___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::AddDecl::l_Lean_addAndCompile;
use crate::r#gen::Lean::Attributes::{
    l_Lean_instBEqAttributeKind_beq, l_Lean_registerBuiltinAttribute,
};
use crate::r#gen::Lean::AuxRecursor::{
    l_Lean_markAuxRecursor, l_Lean_markSparseCasesOn, l_Lean_mkCasesOnName,
};
use crate::r#gen::Lean::CoreM::l_Lean_mkArrow;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::{
    l_Lean_ConstantInfo_levelParams, l_Lean_InductiveVal_numCtors, l_Lean_mkRecName,
};
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::Elab::App::{
    initialize_Lean_Elab_App, l_Lean_Elab_Term_elabAsElim, runtime_initialize_Lean_Elab_App,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_EnvExtension_asyncMayModify___redArg, l_Lean_Environment_asyncPrefix_x3f,
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f, l_Lean_Environment_findConstVal_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_hasUnsafe,
    l_Lean_Environment_header, l_Lean_Environment_setExporting,
    l_Lean_EnvironmentHeader_moduleNames, l_Lean_PersistentEnvExtension_addEntry___redArg,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21,
    l_Lean_Expr_constLevels_x21, l_Lean_Expr_isAppOfArity, l_Lean_Expr_sort___override,
    l_Lean_instInhabitedExpr, l_Lean_mkApp3, l_Lean_mkAppB, l_Lean_mkAppN, l_Lean_mkConst,
    l_Lean_mkRawNatLit,
};
use crate::r#gen::Lean::Level::{
    l_Lean_Level_normalize, l_Lean_Level_ofNat, l_Lean_mkLevelMax, l_Lean_mkLevelMax_x27,
    l_Lean_mkLevelParam,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_nil, l_Lean_MessageData_note, l_Lean_MessageData_ofConstName,
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    l_Lean_Meta_mkEq, l_Lean_Meta_mkEqNDRec, l_Lean_Meta_mkEqSymm,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp,
    l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, l_Lean_Meta_mkLambdaFVars,
    runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::CompletionName::{
    initialize_Lean_Meta_CompletionName, l_Lean_Meta_addToCompletionBlackList,
    runtime_initialize_Lean_Meta_CompletionName,
};
use crate::r#gen::Lean::Meta::Constructions::CtorIdx::{
    initialize_Lean_Meta_Constructions_CtorIdx, l_mkCtorIdx, l_mkCtorIdxName,
    runtime_initialize_Lean_Meta_Constructions_CtorIdx,
};
use crate::r#gen::Lean::Meta::InferType::{l_Lean_Meta_getLevel, l_Lean_Meta_isPropFormerType};
use crate::r#gen::Lean::Meta::NatTable::{
    initialize_Lean_Meta_NatTable, l_mkNatLookupTable, runtime_initialize_Lean_Meta_NatTable,
};
use crate::r#gen::Lean::Modifiers::l_Lean_addProtected;
use crate::r#gen::Lean::PrivateName::{
    l_Lean_isPrivateName, l_Lean_privateToUserName, lean_private_prefix,
};
use crate::r#gen::Lean::ReducibilityAttrs::l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax___closed__0_value
) as *mut leanh::LeanObject;
pub static l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0_value:
    leanh::LeanStringObject<33> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67, 111, 110, 115, 116, 114, 117, 99, 116, 105,
        111, 110, 115, 46, 67, 116, 111, 114, 69, 108, 105, 109, 0,
    ],
};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__1_value:
    leanh::LeanStringObject<59> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 59,
    m_capacity: 59,
    m_length: 58,
    m_data: [
        95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67,
        111, 110, 115, 116, 114, 117, 99, 116, 105, 111, 110, 115, 46, 67, 116, 111, 114, 69, 108,
        105, 109, 46, 48, 46, 76, 101, 97, 110, 46, 109, 97, 120, 76, 101, 118, 101, 108, 115, 0,
    ],
};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__2_value:
    leanh::LeanStringObject<36> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 101, 115, 46, 115, 105, 122, 101, 32, 62, 32, 48, 10, 32, 32, 0,
    ],
};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__2_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__0_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [80, 85, 76, 105, 102, 116, 0],
};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__0_value
        ) as *mut leanh::LeanObject,
        7722212394085076321 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__0_value:
    leanh::LeanStringObject<43> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 43,
    m_capacity: 43,
    m_length: 42,
    m_data: [
        119, 105, 116, 104, 77, 107, 80, 85, 76, 105, 102, 116, 85, 112, 58, 32, 101, 120, 112,
        101, 99, 116, 101, 100, 32, 80, 85, 76, 105, 102, 116, 32, 116, 121, 112, 101, 44, 32, 103,
        111, 116, 32, 0,
    ],
};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__0_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__2_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [117, 112, 0],
};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__2_value
) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__0_value) as *mut leanh::LeanObject,7722212394085076321 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__2_value) as *mut leanh::LeanObject,1200183649597683829 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__0_value:
    leanh::LeanStringObject<39> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        109, 107, 85, 76, 105, 102, 116, 68, 111, 119, 110, 58, 32, 101, 120, 112, 101, 99, 116,
        101, 100, 32, 85, 76, 105, 102, 116, 32, 116, 121, 112, 101, 44, 32, 103, 111, 116, 32, 0,
    ],
};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__0_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__2_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [100, 111, 119, 110, 0],
};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__2_value
) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__3_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__0_value
        ) as *mut leanh::LeanObject,
        7722212394085076321 as *mut leanh::LeanObject,
    ],
};
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__2_value) as *mut leanh::LeanObject,15160637401009616787 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__3_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName___closed__0_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [99, 116, 111, 114, 69, 108, 105, 109, 84, 121, 112, 101, 0]};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_mkCtorElimName___closed__0_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [99, 116, 111, 114, 69, 108, 105, 109, 0],
    };
static mut l_Lean_mkCtorElimName___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkCtorElimName___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_mkConstructorElimName___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [101, 108, 105, 109, 0],
    };
static mut l_Lean_mkConstructorElimName___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkConstructorElimName___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [99, 116, 111, 114, 73, 100, 120, 0]};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__0_value) as *mut leanh::LeanObject,5328818486479589402 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 97, 116, 0]};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__2_value) as *mut leanh::LeanObject,11442535297760353691 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__0_value:
    leanh::LeanStringObject<64> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 64,
    m_capacity: 64,
    m_length: 63,
    m_data: [
        95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67,
        111, 110, 115, 116, 114, 117, 99, 116, 105, 111, 110, 115, 46, 67, 116, 111, 114, 69, 108,
        105, 109, 46, 48, 46, 76, 101, 97, 110, 46, 109, 107, 67, 116, 111, 114, 69, 108, 105, 109,
        84, 121, 112, 101, 0,
    ],
};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__1_value:
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
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__1_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___closed__0_value) as *mut leanh::LeanObject,16122875713692181903 as *mut leanh::LeanObject] };
static mut l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___closed__1_value) as *mut leanh::LeanObject;
pub static l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [104, 0]};
static mut l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject,8738205681931236784 as *mut leanh::LeanObject] };
static mut l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [107, 0]};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___closed__0_value) as *mut leanh::LeanObject,11764356134424884321 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__0_value:
    leanh::LeanStringObject<63> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 63,
    m_capacity: 63,
    m_length: 62,
    m_data: [
        95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67,
        111, 110, 115, 116, 114, 117, 99, 116, 105, 111, 110, 115, 46, 67, 116, 111, 114, 69, 108,
        105, 109, 46, 48, 46, 76, 101, 97, 110, 46, 109, 107, 73, 110, 100, 67, 116, 111, 114, 69,
        108, 105, 109, 0,
    ],
};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__1_value:
    leanh::LeanStringObject<40> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 117, 110, 105, 118, 101, 114, 115,
        101, 32, 108, 101, 118, 101, 108, 115, 32, 111, 110, 32, 96, 99, 97, 115, 101, 115, 79,
        110, 96, 0,
    ],
};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__1_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__0_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [67, 97, 110, 110, 111, 116, 32, 97, 100, 100, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__2_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 116, 111, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__4_value: leanh::LeanStringObject<38> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [96, 32, 98, 101, 99, 97, 117, 115, 101, 32, 105, 116, 32, 105, 115, 32, 105, 110, 32, 97, 110, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 109, 111, 100, 117, 108, 101, 0]};
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__0_value: leanh::LeanStringObject<51> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 51, m_capacity: 51, m_length: 50, m_data: [96, 32, 98, 101, 99, 97, 117, 115, 101, 32, 105, 116, 32, 105, 115, 32, 110, 111, 116, 32, 102, 114, 111, 109, 32, 116, 104, 101, 32, 112, 114, 101, 115, 101, 110, 116, 32, 97, 115, 121, 110, 99, 32, 99, 111, 110, 116, 101, 120, 116, 0]};
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__2_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [32, 96, 0]};
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__0_value: leanh::LeanStringObject<67> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 67, m_capacity: 67, m_length: 66, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67, 111, 110, 115, 116, 114, 117, 99, 116, 105, 111, 110, 115, 46, 67, 116, 111, 114, 69, 108, 105, 109, 46, 48, 46, 76, 101, 97, 110, 46, 109, 107, 67, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 69, 108, 105, 109, 0]};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__0_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__0_value: leanh::LeanStringObject<38> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 115, 99, 111, 112, 101, 58, 32, 65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__2_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [93, 96, 32, 109, 117, 115, 116, 32, 98, 101, 32, 103, 108, 111, 98, 97, 108, 44, 32, 110, 111, 116, 32, 96, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__4_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [103, 108, 111, 98, 97, 108, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__5_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 111, 99, 97, 108, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__6_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 99, 111, 112, 101, 100, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*0 + 24) as u16, other: 0, tag: 0 }, m_objs: [282574488338432 as *mut leanh::LeanObject,72621647814721793 as *mut leanh::LeanObject,65793 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: u64 = 0;
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__6_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__6_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0]};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13556645696814629918 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [67, 111, 110, 115, 116, 114, 117, 99, 116, 105, 111, 110, 115, 0]};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6298619751691480032 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 116, 111, 114, 69, 108, 105, 109, 0]};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,3786691475400949111 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,10175523786497186186 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,844071092489871499 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13546035167488181818 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1091179269233873075 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5544238724718904990 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9300916904073826698 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9360958264282695428 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17029537460416449195 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 299025572 as usize) << 1) | 1) as *mut leanh::LeanObject,7778799843855153382 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,18442512210578991393 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15672496894956456217 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,14401293708838899524 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [103, 101, 110, 95, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 95, 101, 108, 105, 109, 115, 0]};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15554330061519822153 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__28_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanClosureObject<3> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 3, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__28_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__28_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__29_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__29_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__29_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__30_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [103, 101, 110, 101, 114, 97, 116, 101, 32, 116, 104, 101, 32, 96, 46, 116, 111, 67, 116, 111, 114, 73, 100, 120, 96, 32, 97, 110, 100, 32, 96, 46, 99, 116, 111, 114, 46, 101, 108, 105, 109, 96, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 115, 32, 102, 111, 114, 32, 116, 104, 101, 32, 103, 105, 118, 101, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 0]};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__30_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__30_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__31_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__30_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,0 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__31_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__31_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__32_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__31_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__28_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__29_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__32_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__32_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value: leanh::LeanStringObject<262> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 262, m_capacity: 262, m_length: 261, m_data: [71, 101, 110, 101, 114, 97, 116, 101, 32, 116, 104, 101, 32, 96, 46, 116, 111, 67, 116, 111, 114, 73, 100, 120, 96, 32, 97, 110, 100, 32, 96, 46, 99, 116, 111, 114, 46, 101, 108, 105, 109, 96, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 115, 32, 102, 111, 114, 32, 116, 104, 101, 32, 103, 105, 118, 101, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 46, 10, 10, 84, 104, 105, 115, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 105, 115, 32, 111, 110, 108, 121, 32, 109, 101, 97, 110, 116, 32, 116, 111, 32, 98, 101, 32, 117, 115, 101, 100, 32, 105, 110, 32, 96, 73, 110, 105, 116, 46, 80, 114, 101, 108, 117, 100, 101, 96, 32, 116, 111, 32, 98, 117, 105, 108, 100, 32, 116, 104, 101, 115, 101, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 105, 111, 110, 115, 32, 102, 111, 114, 10, 116, 121, 112, 101, 115, 32, 119, 104, 101, 114, 101, 32, 119, 101, 32, 100, 105, 100, 32, 110, 111, 116, 32, 103, 101, 110, 101, 114, 97, 116, 101, 32, 116, 104, 101, 109, 32, 105, 109, 109, 101, 100, 105, 97, 116, 101, 108, 121, 32, 40, 100, 117, 101, 32, 116, 111, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 103, 101, 110, 67, 116, 111, 114, 73, 100, 120, 32, 102, 97, 108, 115, 101, 96, 41, 46, 10, 0]};
static mut l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax_maxArgs(
    mut v_l_3363_: *mut leanh::LeanObject,
    mut v_lvls_3364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_l_3363_) == 2 {
                    v_a_3365_ = leanh::lean_ctor_get(v_l_3363_, 0);
                    leanh::lean_inc(v_a_3365_);
                    v_a_3366_ = leanh::lean_ctor_get(v_l_3363_, 1);
                    leanh::lean_inc(v_a_3366_);
                    leanh::lean_dec_ref_known(v_l_3363_, 2);
                    v___x_3367_ =
                        l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax_maxArgs(
                            v_a_3365_,
                            v_lvls_3364_,
                        );
                    v_l_3363_ = v_a_3366_;
                    v_lvls_3364_ = v___x_3367_;
                    state = 0;
                    continue;
                } else {
                    v___x_3369_ = lean_array_push(v_lvls_3364_, v_l_3363_);
                    return v___x_3369_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax_spec__0(
    mut v_as_3370_: *mut leanh::LeanObject,
    mut v_i_3371_: usize,
    mut v_stop_3372_: usize,
    mut v_b_3373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3374_: u8 = 0;
    let mut v___x_3375_: usize = 0;
    let mut v___x_3376_: usize = 0;
    let mut v___x_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3374_ = lean_usize_dec_eq(v_i_3371_, v_stop_3372_);
                if v___x_3374_ == 0 {
                    v___x_3375_ = 1usize;
                    v___x_3376_ = lean_usize_sub(v_i_3371_, v___x_3375_);
                    v___x_3377_ = lean_array_uget_borrowed(v_as_3370_, v___x_3376_);
                    leanh::lean_inc(v___x_3377_);
                    v___x_3378_ = l_Lean_mkLevelMax(v___x_3377_, v_b_3373_);
                    v_i_3371_ = v___x_3376_;
                    v_b_3373_ = v___x_3378_;
                    state = 0;
                    continue;
                } else {
                    return v_b_3373_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax_spec__0___boxed(
    mut v_as_3380_: *mut leanh::LeanObject,
    mut v_i_3381_: *mut leanh::LeanObject,
    mut v_stop_3382_: *mut leanh::LeanObject,
    mut v_b_3383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3384_: usize = 0;
    let mut v_stop_boxed_3385_: usize = 0;
    let mut v_res_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3384_ = leanh::lean_unbox_usize(v_i_3381_);
    leanh::lean_dec(v_i_3381_);
    v_stop_boxed_3385_ = leanh::lean_unbox_usize(v_stop_3382_);
    leanh::lean_dec(v_stop_3382_);
    v_res_3386_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax_spec__0(v_as_3380_, v_i_boxed_3384_, v_stop_boxed_3385_, v_b_3383_);
    leanh::lean_dec_ref(v_as_3380_);
    return v_res_3386_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax(
    mut v_l_3389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lvls_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_last_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: u8 = 0;
    v___x_3390_ = leanh::lean_box(0);
    v___x_3391_ = leanh::lean_unsigned_to_nat(0);
    v___x_3392_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax___closed__0;
    v_lvls_3393_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax_maxArgs(
        v_l_3389_,
        v___x_3392_,
    );
    v___x_3394_ = lean_array_get_size(v_lvls_3393_);
    v___x_3395_ = leanh::lean_unsigned_to_nat(1);
    v___x_3396_ = lean_nat_sub(v___x_3394_, v___x_3395_);
    v_last_3397_ = lean_array_get(v___x_3390_, v_lvls_3393_, v___x_3396_);
    leanh::lean_dec(v___x_3396_);
    v___x_3398_ = lean_array_pop(v_lvls_3393_);
    v___x_3399_ = lean_array_get_size(v___x_3398_);
    v___x_3400_ = lean_nat_dec_lt(v___x_3391_, v___x_3399_);
    if v___x_3400_ == 0 {
        leanh::lean_dec_ref(v___x_3398_);
        return v_last_3397_;
    } else {
        let mut v___x_3401_: usize = 0;
        let mut v___x_3402_: usize = 0;
        let mut v___x_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3401_ = lean_usize_of_nat(v___x_3399_);
        v___x_3402_ = 0usize;
        v___x_3403_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax_spec__0(v___x_3398_, v___x_3401_, v___x_3402_, v_last_3397_);
        leanh::lean_dec_ref(v___x_3398_);
        return v___x_3403_;
    }
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0(
    mut v_msg_3405_: *mut leanh::LeanObject,
    mut v___y_3406_: *mut leanh::LeanObject,
    mut v___y_3407_: *mut leanh::LeanObject,
    mut v___y_3408_: *mut leanh::LeanObject,
    mut v___y_3409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578__overap_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3411_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0___closed__0;
    v___x_1578__overap_3412_ = lean_panic_fn_borrowed(v___f_3411_, v_msg_3405_);
    leanh::lean_inc(v___y_3409_);
    leanh::lean_inc_ref(v___y_3408_);
    leanh::lean_inc(v___y_3407_);
    leanh::lean_inc_ref(v___y_3406_);
    v___x_3413_ = leanh::lean_apply_5(
        v___x_1578__overap_3412_,
        v___y_3406_,
        v___y_3407_,
        v___y_3408_,
        v___y_3409_,
        leanh::lean_box(0),
    );
    return v___x_3413_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0___boxed(
    mut v_msg_3414_: *mut leanh::LeanObject,
    mut v___y_3415_: *mut leanh::LeanObject,
    mut v___y_3416_: *mut leanh::LeanObject,
    mut v___y_3417_: *mut leanh::LeanObject,
    mut v___y_3418_: *mut leanh::LeanObject,
    mut v___y_3419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3420_ =
        l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0(
            v_msg_3414_,
            v___y_3415_,
            v___y_3416_,
            v___y_3417_,
            v___y_3418_,
        );
    leanh::lean_dec(v___y_3418_);
    leanh::lean_dec_ref(v___y_3417_);
    leanh::lean_dec(v___y_3416_);
    leanh::lean_dec_ref(v___y_3415_);
    return v_res_3420_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1___redArg(
    mut v_a_3421_: *mut leanh::LeanObject,
    mut v_b_3422_: *mut leanh::LeanObject,
    mut v___y_3423_: *mut leanh::LeanObject,
    mut v___y_3424_: *mut leanh::LeanObject,
    mut v___y_3425_: *mut leanh::LeanObject,
    mut v___y_3426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3433_: u8 = 0;
    let mut v___x_3434_: u8 = 0;
    let mut v___x_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3446_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3428_ = leanh::lean_ctor_get(v_a_3421_, 0);
                v_start_3429_ = leanh::lean_ctor_get(v_a_3421_, 1);
                v_stop_3430_ = leanh::lean_ctor_get(v_a_3421_, 2);
                v_isSharedCheck_3446_ = (!leanh::lean_is_exclusive(v_a_3421_)) as u8;
                if v_isSharedCheck_3446_ == 0 {
                    v___x_3432_ = v_a_3421_;
                    v_isShared_3433_ = v_isSharedCheck_3446_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_stop_3430_);
                    leanh::lean_inc(v_start_3429_);
                    leanh::lean_inc(v_array_3428_);
                    leanh::lean_dec(v_a_3421_);
                    v___x_3432_ = leanh::lean_box(0);
                    v_isShared_3433_ = v_isSharedCheck_3446_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3434_ = lean_nat_dec_lt(v_start_3429_, v_stop_3430_);
                if v___x_3434_ == 0 {
                    leanh::lean_del_object(v___x_3432_);
                    leanh::lean_dec(v_stop_3430_);
                    leanh::lean_dec(v_start_3429_);
                    leanh::lean_dec_ref(v_array_3428_);
                    v___x_3435_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3435_, 0, v_b_3422_);
                    return v___x_3435_;
                } else {
                    v___x_3436_ = lean_array_fget_borrowed(v_array_3428_, v_start_3429_);
                    leanh::lean_inc(v___x_3436_);
                    v___x_3437_ = l_Lean_Meta_getLevel(
                        v___x_3436_,
                        v___y_3423_,
                        v___y_3424_,
                        v___y_3425_,
                        v___y_3426_,
                    );
                    if leanh::lean_obj_tag(v___x_3437_) == 0 {
                        v_a_3438_ = leanh::lean_ctor_get(v___x_3437_, 0);
                        leanh::lean_inc(v_a_3438_);
                        leanh::lean_dec_ref_known(v___x_3437_, 1);
                        v___x_3439_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3440_ = lean_nat_add(v_start_3429_, v___x_3439_);
                        leanh::lean_dec(v_start_3429_);
                        if v_isShared_3433_ == 0 {
                            leanh::lean_ctor_set(v___x_3432_, 1, v___x_3440_);
                            v___x_3442_ = v___x_3432_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3445_ =
                                leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_array_3428_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3445_, 1, v___x_3440_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3445_, 2, v_stop_3430_);
                            v___x_3442_ = v_reuseFailAlloc_3445_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_3432_);
                        leanh::lean_dec(v_stop_3430_);
                        leanh::lean_dec(v_start_3429_);
                        leanh::lean_dec_ref(v_array_3428_);
                        leanh::lean_dec(v_b_3422_);
                        return v___x_3437_;
                    }
                }
            }
            2 => {
                v___x_3443_ = l_Lean_mkLevelMax_x27(v_b_3422_, v_a_3438_);
                v_a_3421_ = v___x_3442_;
                v_b_3422_ = v___x_3443_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1___redArg___boxed(
    mut v_a_3447_: *mut leanh::LeanObject,
    mut v_b_3448_: *mut leanh::LeanObject,
    mut v___y_3449_: *mut leanh::LeanObject,
    mut v___y_3450_: *mut leanh::LeanObject,
    mut v___y_3451_: *mut leanh::LeanObject,
    mut v___y_3452_: *mut leanh::LeanObject,
    mut v___y_3453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3454_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1___redArg(v_a_3447_, v_b_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_);
    leanh::lean_dec(v___y_3452_);
    leanh::lean_dec_ref(v___y_3451_);
    leanh::lean_dec(v___y_3450_);
    leanh::lean_dec_ref(v___y_3449_);
    return v_res_3454_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3458_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__2;
    v___x_3459_ = leanh::lean_unsigned_to_nat(2);
    v___x_3460_ = leanh::lean_unsigned_to_nat(32);
    v___x_3461_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__1;
    v___x_3462_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0;
    v___x_3463_ = l_mkPanicMessageWithDecl(
        v___x_3462_,
        v___x_3461_,
        v___x_3460_,
        v___x_3459_,
        v___x_3458_,
    );
    return v___x_3463_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels(
    mut v_es_3464_: *mut leanh::LeanObject,
    mut v_a_3465_: *mut leanh::LeanObject,
    mut v_a_3466_: *mut leanh::LeanObject,
    mut v_a_3467_: *mut leanh::LeanObject,
    mut v_a_3468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: u8 = 0;
    let mut v___x_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3485_: u8 = 0;
    let mut v___x_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3491_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3470_ = leanh::lean_unsigned_to_nat(0);
                v___x_3471_ = lean_array_get_size(v_es_3464_);
                v___x_3472_ = lean_nat_dec_lt(v___x_3470_, v___x_3471_);
                if v___x_3472_ == 0 {
                    leanh::lean_dec_ref(v_es_3464_);
                    v___x_3473_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__3_once), _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__3);
                    v___x_3474_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0(v___x_3473_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_);
                    return v___x_3474_;
                } else {
                    v___x_3475_ = l_Lean_instInhabitedExpr;
                    v___x_3476_ = lean_array_get_borrowed(v___x_3475_, v_es_3464_, v___x_3470_);
                    leanh::lean_inc(v___x_3476_);
                    v___x_3477_ = l_Lean_Meta_getLevel(
                        v___x_3476_,
                        v_a_3465_,
                        v_a_3466_,
                        v_a_3467_,
                        v_a_3468_,
                    );
                    if leanh::lean_obj_tag(v___x_3477_) == 0 {
                        v_a_3478_ = leanh::lean_ctor_get(v___x_3477_, 0);
                        leanh::lean_inc(v_a_3478_);
                        leanh::lean_dec_ref_known(v___x_3477_, 1);
                        v___x_3479_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3480_ =
                            l_Array_toSubarray___redArg(v_es_3464_, v___x_3479_, v___x_3471_);
                        v___x_3481_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1___redArg(v___x_3480_, v_a_3478_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_);
                        if leanh::lean_obj_tag(v___x_3481_) == 0 {
                            v_a_3482_ = leanh::lean_ctor_get(v___x_3481_, 0);
                            v_isSharedCheck_3491_ =
                                (!leanh::lean_is_exclusive(v___x_3481_)) as u8;
                            if v_isSharedCheck_3491_ == 0 {
                                v___x_3484_ = v___x_3481_;
                                v_isShared_3485_ = v_isSharedCheck_3491_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3482_);
                                leanh::lean_dec(v___x_3481_);
                                v___x_3484_ = leanh::lean_box(0);
                                v_isShared_3485_ = v_isSharedCheck_3491_;
                                state = 1;
                                continue;
                            }
                        } else {
                            return v___x_3481_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_es_3464_);
                        return v___x_3477_;
                    }
                }
            }
            1 => {
                v___x_3486_ = l_Lean_Level_normalize(v_a_3482_);
                leanh::lean_dec(v_a_3482_);
                v___x_3487_ =
                    l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax(v___x_3486_);
                if v_isShared_3485_ == 0 {
                    leanh::lean_ctor_set(v___x_3484_, 0, v___x_3487_);
                    v___x_3489_ = v___x_3484_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3490_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3490_, 0, v___x_3487_);
                    v___x_3489_ = v_reuseFailAlloc_3490_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3489_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___boxed(
    mut v_es_3492_: *mut leanh::LeanObject,
    mut v_a_3493_: *mut leanh::LeanObject,
    mut v_a_3494_: *mut leanh::LeanObject,
    mut v_a_3495_: *mut leanh::LeanObject,
    mut v_a_3496_: *mut leanh::LeanObject,
    mut v_a_3497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3498_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels(
        v_es_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_,
    );
    leanh::lean_dec(v_a_3496_);
    leanh::lean_dec_ref(v_a_3495_);
    leanh::lean_dec(v_a_3494_);
    leanh::lean_dec_ref(v_a_3493_);
    return v_res_3498_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1(
    mut v_inst_3499_: *mut leanh::LeanObject,
    mut v_R_3500_: *mut leanh::LeanObject,
    mut v_a_3501_: *mut leanh::LeanObject,
    mut v_b_3502_: *mut leanh::LeanObject,
    mut v_c_3503_: *mut leanh::LeanObject,
    mut v___y_3504_: *mut leanh::LeanObject,
    mut v___y_3505_: *mut leanh::LeanObject,
    mut v___y_3506_: *mut leanh::LeanObject,
    mut v___y_3507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3509_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1___redArg(v_a_3501_, v_b_3502_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_);
    return v___x_3509_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1___boxed(
    mut v_inst_3510_: *mut leanh::LeanObject,
    mut v_R_3511_: *mut leanh::LeanObject,
    mut v_a_3512_: *mut leanh::LeanObject,
    mut v_b_3513_: *mut leanh::LeanObject,
    mut v_c_3514_: *mut leanh::LeanObject,
    mut v___y_3515_: *mut leanh::LeanObject,
    mut v___y_3516_: *mut leanh::LeanObject,
    mut v___y_3517_: *mut leanh::LeanObject,
    mut v___y_3518_: *mut leanh::LeanObject,
    mut v___y_3519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3520_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__1(v_inst_3510_, v_R_3511_, v_a_3512_, v_b_3513_, v_c_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_);
    leanh::lean_dec(v___y_3518_);
    leanh::lean_dec_ref(v___y_3517_);
    leanh::lean_dec(v___y_3516_);
    leanh::lean_dec_ref(v___y_3515_);
    return v_res_3520_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift(
    mut v_r_3524_: *mut leanh::LeanObject,
    mut v_t_3525_: *mut leanh::LeanObject,
    mut v_a_3526_: *mut leanh::LeanObject,
    mut v_a_3527_: *mut leanh::LeanObject,
    mut v_a_3528_: *mut leanh::LeanObject,
    mut v_a_3529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3535_: u8 = 0;
    let mut v___x_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3545_: u8 = 0;
    let mut v_a_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3549_: u8 = 0;
    let mut v___x_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3553_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_t_3525_);
                v___x_3531_ =
                    l_Lean_Meta_getLevel(v_t_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_);
                if leanh::lean_obj_tag(v___x_3531_) == 0 {
                    v_a_3532_ = leanh::lean_ctor_get(v___x_3531_, 0);
                    v_isSharedCheck_3545_ = (!leanh::lean_is_exclusive(v___x_3531_)) as u8;
                    if v_isSharedCheck_3545_ == 0 {
                        v___x_3534_ = v___x_3531_;
                        v_isShared_3535_ = v_isSharedCheck_3545_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3532_);
                        leanh::lean_dec(v___x_3531_);
                        v___x_3534_ = leanh::lean_box(0);
                        v_isShared_3535_ = v_isSharedCheck_3545_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_t_3525_);
                    leanh::lean_dec(v_r_3524_);
                    v_a_3546_ = leanh::lean_ctor_get(v___x_3531_, 0);
                    v_isSharedCheck_3553_ = (!leanh::lean_is_exclusive(v___x_3531_)) as u8;
                    if v_isSharedCheck_3553_ == 0 {
                        v___x_3548_ = v___x_3531_;
                        v_isShared_3549_ = v_isSharedCheck_3553_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3546_);
                        leanh::lean_dec(v___x_3531_);
                        v___x_3548_ = leanh::lean_box(0);
                        v_isShared_3549_ = v_isSharedCheck_3553_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3536_ =
                    l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__1;
                v___x_3537_ = leanh::lean_box(0);
                v___x_3538_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3538_, 0, v_a_3532_);
                leanh::lean_ctor_set(v___x_3538_, 1, v___x_3537_);
                v___x_3539_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3539_, 0, v_r_3524_);
                leanh::lean_ctor_set(v___x_3539_, 1, v___x_3538_);
                v___x_3540_ = l_Lean_mkConst(v___x_3536_, v___x_3539_);
                v___x_3541_ = l_Lean_Expr_app___override(v___x_3540_, v_t_3525_);
                if v_isShared_3535_ == 0 {
                    leanh::lean_ctor_set(v___x_3534_, 0, v___x_3541_);
                    v___x_3543_ = v___x_3534_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3544_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3544_, 0, v___x_3541_);
                    v___x_3543_ = v_reuseFailAlloc_3544_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3543_;
            }
            3 => {
                if v_isShared_3549_ == 0 {
                    v___x_3551_ = v___x_3548_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3552_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_a_3546_);
                    v___x_3551_ = v_reuseFailAlloc_3552_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3551_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___boxed(
    mut v_r_3554_: *mut leanh::LeanObject,
    mut v_t_3555_: *mut leanh::LeanObject,
    mut v_a_3556_: *mut leanh::LeanObject,
    mut v_a_3557_: *mut leanh::LeanObject,
    mut v_a_3558_: *mut leanh::LeanObject,
    mut v_a_3559_: *mut leanh::LeanObject,
    mut v_a_3560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3561_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift(
        v_r_3554_, v_t_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_,
    );
    leanh::lean_dec(v_a_3559_);
    leanh::lean_dec_ref(v_a_3558_);
    leanh::lean_dec(v_a_3557_);
    leanh::lean_dec_ref(v_a_3556_);
    return v_res_3561_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0_spec__0(
    mut v_msgData_3562_: *mut leanh::LeanObject,
    mut v___y_3563_: *mut leanh::LeanObject,
    mut v___y_3564_: *mut leanh::LeanObject,
    mut v___y_3565_: *mut leanh::LeanObject,
    mut v___y_3566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3568_ = lean_st_ref_get(v___y_3566_);
    v_env_3569_ = leanh::lean_ctor_get(v___x_3568_, 0);
    leanh::lean_inc_ref(v_env_3569_);
    leanh::lean_dec(v___x_3568_);
    v___x_3570_ = lean_st_ref_get(v___y_3564_);
    v_mctx_3571_ = leanh::lean_ctor_get(v___x_3570_, 0);
    leanh::lean_inc_ref(v_mctx_3571_);
    leanh::lean_dec(v___x_3570_);
    v_lctx_3572_ = leanh::lean_ctor_get(v___y_3563_, 2);
    v_options_3573_ = leanh::lean_ctor_get(v___y_3565_, 2);
    leanh::lean_inc_ref(v_options_3573_);
    leanh::lean_inc_ref(v_lctx_3572_);
    v___x_3574_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3574_, 0, v_env_3569_);
    leanh::lean_ctor_set(v___x_3574_, 1, v_mctx_3571_);
    leanh::lean_ctor_set(v___x_3574_, 2, v_lctx_3572_);
    leanh::lean_ctor_set(v___x_3574_, 3, v_options_3573_);
    v___x_3575_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3575_, 0, v___x_3574_);
    leanh::lean_ctor_set(v___x_3575_, 1, v_msgData_3562_);
    v___x_3576_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3576_, 0, v___x_3575_);
    return v___x_3576_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0_spec__0___boxed(
    mut v_msgData_3577_: *mut leanh::LeanObject,
    mut v___y_3578_: *mut leanh::LeanObject,
    mut v___y_3579_: *mut leanh::LeanObject,
    mut v___y_3580_: *mut leanh::LeanObject,
    mut v___y_3581_: *mut leanh::LeanObject,
    mut v___y_3582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3583_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0_spec__0(v_msgData_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
    leanh::lean_dec(v___y_3581_);
    leanh::lean_dec_ref(v___y_3580_);
    leanh::lean_dec(v___y_3579_);
    leanh::lean_dec_ref(v___y_3578_);
    return v_res_3583_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(
    mut v_msg_3584_: *mut leanh::LeanObject,
    mut v___y_3585_: *mut leanh::LeanObject,
    mut v___y_3586_: *mut leanh::LeanObject,
    mut v___y_3587_: *mut leanh::LeanObject,
    mut v___y_3588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3595_: u8 = 0;
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3600_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3590_ = leanh::lean_ctor_get(v___y_3587_, 5);
                v___x_3591_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0_spec__0(v_msg_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_);
                v_a_3592_ = leanh::lean_ctor_get(v___x_3591_, 0);
                v_isSharedCheck_3600_ = (!leanh::lean_is_exclusive(v___x_3591_)) as u8;
                if v_isSharedCheck_3600_ == 0 {
                    v___x_3594_ = v___x_3591_;
                    v_isShared_3595_ = v_isSharedCheck_3600_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3592_);
                    leanh::lean_dec(v___x_3591_);
                    v___x_3594_ = leanh::lean_box(0);
                    v_isShared_3595_ = v_isSharedCheck_3600_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_3590_);
                v___x_3596_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3596_, 0, v_ref_3590_);
                leanh::lean_ctor_set(v___x_3596_, 1, v_a_3592_);
                if v_isShared_3595_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3594_, 1);
                    leanh::lean_ctor_set(v___x_3594_, 0, v___x_3596_);
                    v___x_3598_ = v___x_3594_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3599_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3599_, 0, v___x_3596_);
                    v___x_3598_ = v_reuseFailAlloc_3599_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3598_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg___boxed(
    mut v_msg_3601_: *mut leanh::LeanObject,
    mut v___y_3602_: *mut leanh::LeanObject,
    mut v___y_3603_: *mut leanh::LeanObject,
    mut v___y_3604_: *mut leanh::LeanObject,
    mut v___y_3605_: *mut leanh::LeanObject,
    mut v___y_3606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3607_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v_msg_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
    leanh::lean_dec(v___y_3605_);
    leanh::lean_dec_ref(v___y_3604_);
    leanh::lean_dec(v___y_3603_);
    leanh::lean_dec_ref(v___y_3602_);
    return v_res_3607_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3609_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__0;
    v___x_3610_ = l_Lean_stringToMessageData(v___x_3609_);
    return v___x_3610_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp(
    mut v_t_3615_: *mut leanh::LeanObject,
    mut v_k_3616_: *mut leanh::LeanObject,
    mut v_a_3617_: *mut leanh::LeanObject,
    mut v_a_3618_: *mut leanh::LeanObject,
    mut v_a_3619_: *mut leanh::LeanObject,
    mut v_a_3620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: u8 = 0;
    let mut v___x_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3636_: u8 = 0;
    let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3645_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_3620_);
                leanh::lean_inc_ref(v_a_3619_);
                leanh::lean_inc(v_a_3618_);
                leanh::lean_inc_ref(v_a_3617_);
                v___x_3622_ = lean_whnf(v_t_3615_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_);
                if leanh::lean_obj_tag(v___x_3622_) == 0 {
                    v_a_3623_ = leanh::lean_ctor_get(v___x_3622_, 0);
                    leanh::lean_inc(v_a_3623_);
                    leanh::lean_dec_ref_known(v___x_3622_, 1);
                    v___x_3624_ =
                        l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__1;
                    v___x_3625_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3626_ = l_Lean_Expr_isAppOfArity(v_a_3623_, v___x_3624_, v___x_3625_);
                    if v___x_3626_ == 0 {
                        leanh::lean_dec_ref(v_k_3616_);
                        v___x_3627_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__1_once), _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__1);
                        v___x_3628_ = l_Lean_MessageData_ofExpr(v_a_3623_);
                        v___x_3629_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3629_, 0, v___x_3627_);
                        leanh::lean_ctor_set(v___x_3629_, 1, v___x_3628_);
                        v___x_3630_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_3629_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_);
                        return v___x_3630_;
                    } else {
                        v___x_3631_ = l_Lean_Expr_appArg_x21(v_a_3623_);
                        leanh::lean_inc(v_a_3620_);
                        leanh::lean_inc_ref(v_a_3619_);
                        leanh::lean_inc(v_a_3618_);
                        leanh::lean_inc_ref(v_a_3617_);
                        leanh::lean_inc_ref(v___x_3631_);
                        v___x_3632_ = leanh::lean_apply_6(
                            v_k_3616_,
                            v___x_3631_,
                            v_a_3617_,
                            v_a_3618_,
                            v_a_3619_,
                            v_a_3620_,
                            leanh::lean_box(0),
                        );
                        if leanh::lean_obj_tag(v___x_3632_) == 0 {
                            v_a_3633_ = leanh::lean_ctor_get(v___x_3632_, 0);
                            v_isSharedCheck_3645_ =
                                (!leanh::lean_is_exclusive(v___x_3632_)) as u8;
                            if v_isSharedCheck_3645_ == 0 {
                                v___x_3635_ = v___x_3632_;
                                v_isShared_3636_ = v_isSharedCheck_3645_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3633_);
                                leanh::lean_dec(v___x_3632_);
                                v___x_3635_ = leanh::lean_box(0);
                                v_isShared_3636_ = v_isSharedCheck_3645_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_3631_);
                            leanh::lean_dec(v_a_3623_);
                            return v___x_3632_;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_k_3616_);
                    return v___x_3622_;
                }
            }
            1 => {
                v___x_3637_ =
                    l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___closed__3;
                v___x_3638_ = l_Lean_Expr_appFn_x21(v_a_3623_);
                leanh::lean_dec(v_a_3623_);
                v___x_3639_ = l_Lean_Expr_constLevels_x21(v___x_3638_);
                leanh::lean_dec_ref(v___x_3638_);
                v___x_3640_ = l_Lean_mkConst(v___x_3637_, v___x_3639_);
                v___x_3641_ = l_Lean_mkAppB(v___x_3640_, v___x_3631_, v_a_3633_);
                if v_isShared_3636_ == 0 {
                    leanh::lean_ctor_set(v___x_3635_, 0, v___x_3641_);
                    v___x_3643_ = v___x_3635_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3644_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3641_);
                    v___x_3643_ = v_reuseFailAlloc_3644_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3643_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp___boxed(
    mut v_t_3646_: *mut leanh::LeanObject,
    mut v_k_3647_: *mut leanh::LeanObject,
    mut v_a_3648_: *mut leanh::LeanObject,
    mut v_a_3649_: *mut leanh::LeanObject,
    mut v_a_3650_: *mut leanh::LeanObject,
    mut v_a_3651_: *mut leanh::LeanObject,
    mut v_a_3652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3653_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp(
        v_t_3646_, v_k_3647_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_,
    );
    leanh::lean_dec(v_a_3651_);
    leanh::lean_dec_ref(v_a_3650_);
    leanh::lean_dec(v_a_3649_);
    leanh::lean_dec_ref(v_a_3648_);
    return v_res_3653_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0(
    mut v_00_u03b1_3654_: *mut leanh::LeanObject,
    mut v_msg_3655_: *mut leanh::LeanObject,
    mut v___y_3656_: *mut leanh::LeanObject,
    mut v___y_3657_: *mut leanh::LeanObject,
    mut v___y_3658_: *mut leanh::LeanObject,
    mut v___y_3659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3661_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v_msg_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_);
    return v___x_3661_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___boxed(
    mut v_00_u03b1_3662_: *mut leanh::LeanObject,
    mut v_msg_3663_: *mut leanh::LeanObject,
    mut v___y_3664_: *mut leanh::LeanObject,
    mut v___y_3665_: *mut leanh::LeanObject,
    mut v___y_3666_: *mut leanh::LeanObject,
    mut v___y_3667_: *mut leanh::LeanObject,
    mut v___y_3668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3669_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0(v_00_u03b1_3662_, v_msg_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_);
    leanh::lean_dec(v___y_3667_);
    leanh::lean_dec_ref(v___y_3666_);
    leanh::lean_dec(v___y_3665_);
    leanh::lean_dec_ref(v___y_3664_);
    return v_res_3669_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3671_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__0;
    v___x_3672_ = l_Lean_stringToMessageData(v___x_3671_);
    return v___x_3672_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown(
    mut v_e_3677_: *mut leanh::LeanObject,
    mut v_a_3678_: *mut leanh::LeanObject,
    mut v_a_3679_: *mut leanh::LeanObject,
    mut v_a_3680_: *mut leanh::LeanObject,
    mut v_a_3681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3689_: u8 = 0;
    let mut v___x_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: u8 = 0;
    let mut v___x_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3706_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_3681_);
                leanh::lean_inc_ref(v_a_3680_);
                leanh::lean_inc(v_a_3679_);
                leanh::lean_inc_ref(v_a_3678_);
                leanh::lean_inc_ref(v_e_3677_);
                v___x_3683_ =
                    lean_infer_type(v_e_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_);
                if leanh::lean_obj_tag(v___x_3683_) == 0 {
                    v_a_3684_ = leanh::lean_ctor_get(v___x_3683_, 0);
                    leanh::lean_inc(v_a_3684_);
                    leanh::lean_dec_ref_known(v___x_3683_, 1);
                    leanh::lean_inc(v_a_3681_);
                    leanh::lean_inc_ref(v_a_3680_);
                    leanh::lean_inc(v_a_3679_);
                    leanh::lean_inc_ref(v_a_3678_);
                    v___x_3685_ = lean_whnf(v_a_3684_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_);
                    if leanh::lean_obj_tag(v___x_3685_) == 0 {
                        v_a_3686_ = leanh::lean_ctor_get(v___x_3685_, 0);
                        v_isSharedCheck_3706_ =
                            (!leanh::lean_is_exclusive(v___x_3685_)) as u8;
                        if v_isSharedCheck_3706_ == 0 {
                            v___x_3688_ = v___x_3685_;
                            v_isShared_3689_ = v_isSharedCheck_3706_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3686_);
                            leanh::lean_dec(v___x_3685_);
                            v___x_3688_ = leanh::lean_box(0);
                            v_isShared_3689_ = v_isSharedCheck_3706_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_3677_);
                        return v___x_3685_;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_3677_);
                    return v___x_3683_;
                }
            }
            1 => {
                v___x_3690_ =
                    l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift___closed__1;
                v___x_3691_ = leanh::lean_unsigned_to_nat(1);
                v___x_3692_ = l_Lean_Expr_isAppOfArity(v_a_3686_, v___x_3690_, v___x_3691_);
                if v___x_3692_ == 0 {
                    leanh::lean_del_object(v___x_3688_);
                    leanh::lean_dec_ref(v_e_3677_);
                    v___x_3693_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__1_once), _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__1);
                    v___x_3694_ = l_Lean_MessageData_ofExpr(v_a_3686_);
                    v___x_3695_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3695_, 0, v___x_3693_);
                    leanh::lean_ctor_set(v___x_3695_, 1, v___x_3694_);
                    v___x_3696_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_3695_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_);
                    return v___x_3696_;
                } else {
                    v___x_3697_ = l_Lean_Expr_appArg_x21(v_a_3686_);
                    v___x_3698_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___closed__3;
                    v___x_3699_ = l_Lean_Expr_appFn_x21(v_a_3686_);
                    leanh::lean_dec(v_a_3686_);
                    v___x_3700_ = l_Lean_Expr_constLevels_x21(v___x_3699_);
                    leanh::lean_dec_ref(v___x_3699_);
                    v___x_3701_ = l_Lean_mkConst(v___x_3698_, v___x_3700_);
                    v___x_3702_ = l_Lean_mkAppB(v___x_3701_, v___x_3697_, v_e_3677_);
                    if v_isShared_3689_ == 0 {
                        leanh::lean_ctor_set(v___x_3688_, 0, v___x_3702_);
                        v___x_3704_ = v___x_3688_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3705_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3705_, 0, v___x_3702_);
                        v___x_3704_ = v_reuseFailAlloc_3705_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3704_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown___boxed(
    mut v_e_3707_: *mut leanh::LeanObject,
    mut v_a_3708_: *mut leanh::LeanObject,
    mut v_a_3709_: *mut leanh::LeanObject,
    mut v_a_3710_: *mut leanh::LeanObject,
    mut v_a_3711_: *mut leanh::LeanObject,
    mut v_a_3712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3713_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown(
        v_e_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_,
    );
    leanh::lean_dec(v_a_3711_);
    leanh::lean_dec_ref(v_a_3710_);
    leanh::lean_dec(v_a_3709_);
    leanh::lean_dec_ref(v_a_3708_);
    return v_res_3713_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting_spec__0(
    mut v_a_3714_: *mut leanh::LeanObject,
    mut v_sz_3715_: usize,
    mut v_i_3716_: usize,
    mut v_bs_3717_: *mut leanh::LeanObject,
    mut v___y_3718_: *mut leanh::LeanObject,
    mut v___y_3719_: *mut leanh::LeanObject,
    mut v___y_3720_: *mut leanh::LeanObject,
    mut v___y_3721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3723_: u8 = 0;
    let mut v___x_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: usize = 0;
    let mut v___x_3731_: usize = 0;
    let mut v___x_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3737_: u8 = 0;
    let mut v___x_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3741_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3723_ = lean_usize_dec_lt(v_i_3716_, v_sz_3715_);
                if v___x_3723_ == 0 {
                    leanh::lean_dec(v_a_3714_);
                    v___x_3724_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3724_, 0, v_bs_3717_);
                    return v___x_3724_;
                } else {
                    v_v_3725_ = lean_array_uget_borrowed(v_bs_3717_, v_i_3716_);
                    leanh::lean_inc(v_v_3725_);
                    leanh::lean_inc(v_a_3714_);
                    v___x_3726_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULift(
                        v_a_3714_,
                        v_v_3725_,
                        v___y_3718_,
                        v___y_3719_,
                        v___y_3720_,
                        v___y_3721_,
                    );
                    if leanh::lean_obj_tag(v___x_3726_) == 0 {
                        v_a_3727_ = leanh::lean_ctor_get(v___x_3726_, 0);
                        leanh::lean_inc(v_a_3727_);
                        leanh::lean_dec_ref_known(v___x_3726_, 1);
                        v___x_3728_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_3729_ = lean_array_uset(v_bs_3717_, v_i_3716_, v___x_3728_);
                        v___x_3730_ = 1usize;
                        v___x_3731_ = lean_usize_add(v_i_3716_, v___x_3730_);
                        v___x_3732_ = lean_array_uset(v_bs_x27_3729_, v_i_3716_, v_a_3727_);
                        v_i_3716_ = v___x_3731_;
                        v_bs_3717_ = v___x_3732_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_3717_);
                        leanh::lean_dec(v_a_3714_);
                        v_a_3734_ = leanh::lean_ctor_get(v___x_3726_, 0);
                        v_isSharedCheck_3741_ =
                            (!leanh::lean_is_exclusive(v___x_3726_)) as u8;
                        if v_isSharedCheck_3741_ == 0 {
                            v___x_3736_ = v___x_3726_;
                            v_isShared_3737_ = v_isSharedCheck_3741_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3734_);
                            leanh::lean_dec(v___x_3726_);
                            v___x_3736_ = leanh::lean_box(0);
                            v_isShared_3737_ = v_isSharedCheck_3741_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3737_ == 0 {
                    v___x_3739_ = v___x_3736_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3740_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_a_3734_);
                    v___x_3739_ = v_reuseFailAlloc_3740_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3739_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting_spec__0___boxed(
    mut v_a_3742_: *mut leanh::LeanObject,
    mut v_sz_3743_: *mut leanh::LeanObject,
    mut v_i_3744_: *mut leanh::LeanObject,
    mut v_bs_3745_: *mut leanh::LeanObject,
    mut v___y_3746_: *mut leanh::LeanObject,
    mut v___y_3747_: *mut leanh::LeanObject,
    mut v___y_3748_: *mut leanh::LeanObject,
    mut v___y_3749_: *mut leanh::LeanObject,
    mut v___y_3750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3751_: usize = 0;
    let mut v_i_boxed_3752_: usize = 0;
    let mut v_res_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3751_ = leanh::lean_unbox_usize(v_sz_3743_);
    leanh::lean_dec(v_sz_3743_);
    v_i_boxed_3752_ = leanh::lean_unbox_usize(v_i_3744_);
    leanh::lean_dec(v_i_3744_);
    v_res_3753_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting_spec__0(v_a_3742_, v_sz_boxed_3751_, v_i_boxed_3752_, v_bs_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_);
    leanh::lean_dec(v___y_3749_);
    leanh::lean_dec_ref(v___y_3748_);
    leanh::lean_dec(v___y_3747_);
    leanh::lean_dec_ref(v___y_3746_);
    return v_res_3753_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3754_ = leanh::lean_unsigned_to_nat(1);
    v___x_3755_ = l_Lean_Level_ofNat(v___x_3754_);
    return v___x_3755_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting(
    mut v_n_3756_: *mut leanh::LeanObject,
    mut v_es_3757_: *mut leanh::LeanObject,
    mut v_a_3758_: *mut leanh::LeanObject,
    mut v_a_3759_: *mut leanh::LeanObject,
    mut v_a_3760_: *mut leanh::LeanObject,
    mut v_a_3761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3767_: usize = 0;
    let mut v___x_3768_: usize = 0;
    let mut v___x_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3778_: u8 = 0;
    let mut v___x_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3782_: u8 = 0;
    let mut v_a_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3786_: u8 = 0;
    let mut v___x_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3790_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_es_3757_);
                v___x_3763_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels(
                    v_es_3757_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_,
                );
                if leanh::lean_obj_tag(v___x_3763_) == 0 {
                    v_a_3764_ = leanh::lean_ctor_get(v___x_3763_, 0);
                    leanh::lean_inc_n(v_a_3764_, 2);
                    leanh::lean_dec_ref_known(v___x_3763_, 1);
                    v___x_3765_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting___closed__0_once), _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting___closed__0);
                    v___x_3766_ = l_Lean_mkLevelMax_x27(v_a_3764_, v___x_3765_);
                    v_sz_3767_ = lean_array_size(v_es_3757_);
                    v___x_3768_ = 0usize;
                    v___x_3769_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting_spec__0(v_a_3764_, v_sz_3767_, v___x_3768_, v_es_3757_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_);
                    if leanh::lean_obj_tag(v___x_3769_) == 0 {
                        v_a_3770_ = leanh::lean_ctor_get(v___x_3769_, 0);
                        leanh::lean_inc(v_a_3770_);
                        leanh::lean_dec_ref_known(v___x_3769_, 1);
                        v___x_3771_ = l_Lean_Level_normalize(v___x_3766_);
                        leanh::lean_dec(v___x_3766_);
                        v___x_3772_ =
                            l___private_Lean_Meta_Constructions_CtorElim_0__Lean_reassocMax(
                                v___x_3771_,
                            );
                        v___x_3773_ = l_Lean_Expr_sort___override(v___x_3772_);
                        v___x_3774_ = l_mkNatLookupTable(
                            v_n_3756_,
                            v___x_3773_,
                            v_a_3770_,
                            v_a_3758_,
                            v_a_3759_,
                            v_a_3760_,
                            v_a_3761_,
                        );
                        leanh::lean_dec(v_a_3770_);
                        return v___x_3774_;
                    } else {
                        leanh::lean_dec(v___x_3766_);
                        leanh::lean_dec_ref(v_n_3756_);
                        v_a_3775_ = leanh::lean_ctor_get(v___x_3769_, 0);
                        v_isSharedCheck_3782_ =
                            (!leanh::lean_is_exclusive(v___x_3769_)) as u8;
                        if v_isSharedCheck_3782_ == 0 {
                            v___x_3777_ = v___x_3769_;
                            v_isShared_3778_ = v_isSharedCheck_3782_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3775_);
                            leanh::lean_dec(v___x_3769_);
                            v___x_3777_ = leanh::lean_box(0);
                            v_isShared_3778_ = v_isSharedCheck_3782_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_es_3757_);
                    leanh::lean_dec_ref(v_n_3756_);
                    v_a_3783_ = leanh::lean_ctor_get(v___x_3763_, 0);
                    v_isSharedCheck_3790_ = (!leanh::lean_is_exclusive(v___x_3763_)) as u8;
                    if v_isSharedCheck_3790_ == 0 {
                        v___x_3785_ = v___x_3763_;
                        v_isShared_3786_ = v_isSharedCheck_3790_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3783_);
                        leanh::lean_dec(v___x_3763_);
                        v___x_3785_ = leanh::lean_box(0);
                        v_isShared_3786_ = v_isSharedCheck_3790_;
                        state = 3;
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
                    v_reuseFailAlloc_3781_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_a_3775_);
                    v___x_3780_ = v_reuseFailAlloc_3781_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3780_;
            }
            3 => {
                if v_isShared_3786_ == 0 {
                    v___x_3788_ = v___x_3785_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3789_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3783_);
                    v___x_3788_ = v_reuseFailAlloc_3789_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3788_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting___boxed(
    mut v_n_3791_: *mut leanh::LeanObject,
    mut v_es_3792_: *mut leanh::LeanObject,
    mut v_a_3793_: *mut leanh::LeanObject,
    mut v_a_3794_: *mut leanh::LeanObject,
    mut v_a_3795_: *mut leanh::LeanObject,
    mut v_a_3796_: *mut leanh::LeanObject,
    mut v_a_3797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3798_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting(
        v_n_3791_, v_es_3792_, v_a_3793_, v_a_3794_, v_a_3795_, v_a_3796_,
    );
    leanh::lean_dec(v_a_3796_);
    leanh::lean_dec_ref(v_a_3795_);
    leanh::lean_dec(v_a_3794_);
    leanh::lean_dec_ref(v_a_3793_);
    return v_res_3798_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName(
    mut v_indName_3800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3801_ =
        l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName___closed__0;
    v___x_3802_ = l_Lean_Name_str___override(v_indName_3800_, v___x_3801_);
    return v___x_3802_;
}
pub unsafe fn l_Lean_mkCtorElimName(
    mut v_indName_3804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3805_ = l_Lean_mkCtorElimName___closed__0;
    v___x_3806_ = l_Lean_Name_str___override(v_indName_3804_, v___x_3805_);
    return v___x_3806_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_asPrivateAs(
    mut v_n1_3807_: *mut leanh::LeanObject,
    mut v_n2_3808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3809_ = lean_private_prefix(v_n2_3808_);
    if leanh::lean_obj_tag(v___x_3809_) == 0 {
        let mut v___x_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3810_ = l_Lean_privateToUserName(v_n1_3807_);
        return v___x_3810_;
    } else {
        let mut v_val_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3811_ = leanh::lean_ctor_get(v___x_3809_, 0);
        leanh::lean_inc(v_val_3811_);
        leanh::lean_dec_ref_known(v___x_3809_, 1);
        v___x_3812_ = l_Lean_privateToUserName(v_n1_3807_);
        v___x_3813_ = l_Lean_Name_appendCore(v_val_3811_, v___x_3812_);
        leanh::lean_dec(v_val_3811_);
        return v___x_3813_;
    }
}
pub unsafe fn l_Lean_mkConstructorElimName(
    mut v_indName_3815_: *mut leanh::LeanObject,
    mut v_conName_3816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3817_ = l_Lean_mkConstructorElimName___closed__0;
    v___x_3818_ = l_Lean_Name_str___override(v_conName_3816_, v___x_3817_);
    v___x_3819_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_asPrivateAs(
        v___x_3818_,
        v_indName_3815_,
    );
    return v___x_3819_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg___lam__0(
    mut v_k_3820_: *mut leanh::LeanObject,
    mut v_b_3821_: *mut leanh::LeanObject,
    mut v_c_3822_: *mut leanh::LeanObject,
    mut v___y_3823_: *mut leanh::LeanObject,
    mut v___y_3824_: *mut leanh::LeanObject,
    mut v___y_3825_: *mut leanh::LeanObject,
    mut v___y_3826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_3826_);
    leanh::lean_inc_ref(v___y_3825_);
    leanh::lean_inc(v___y_3824_);
    leanh::lean_inc_ref(v___y_3823_);
    v___x_3828_ = leanh::lean_apply_7(
        v_k_3820_,
        v_b_3821_,
        v_c_3822_,
        v___y_3823_,
        v___y_3824_,
        v___y_3825_,
        v___y_3826_,
        leanh::lean_box(0),
    );
    return v___x_3828_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg___lam__0___boxed(
    mut v_k_3829_: *mut leanh::LeanObject,
    mut v_b_3830_: *mut leanh::LeanObject,
    mut v_c_3831_: *mut leanh::LeanObject,
    mut v___y_3832_: *mut leanh::LeanObject,
    mut v___y_3833_: *mut leanh::LeanObject,
    mut v___y_3834_: *mut leanh::LeanObject,
    mut v___y_3835_: *mut leanh::LeanObject,
    mut v___y_3836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3837_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg___lam__0(v_k_3829_, v_b_3830_, v_c_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
    leanh::lean_dec(v___y_3835_);
    leanh::lean_dec_ref(v___y_3834_);
    leanh::lean_dec(v___y_3833_);
    leanh::lean_dec_ref(v___y_3832_);
    return v_res_3837_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(
    mut v_type_3838_: *mut leanh::LeanObject,
    mut v_k_3839_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_3840_: u8,
    mut v___y_3841_: *mut leanh::LeanObject,
    mut v___y_3842_: *mut leanh::LeanObject,
    mut v___y_3843_: *mut leanh::LeanObject,
    mut v___y_3844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: u8 = 0;
    let mut v___x_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3853_: u8 = 0;
    let mut v___x_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3857_: u8 = 0;
    let mut v_a_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3861_: u8 = 0;
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3865_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3846_ = leanh::lean_alloc_closure(l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_3846_, 0, v_k_3839_);
                v___x_3847_ = 0;
                v___x_3848_ = leanh::lean_box(0);
                v___x_3849_ =
                    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                        leanh::lean_box(0),
                        v___x_3847_,
                        v___x_3848_,
                        v_type_3838_,
                        v___f_3846_,
                        v_cleanupAnnotations_3840_,
                        v___x_3847_,
                        v___y_3841_,
                        v___y_3842_,
                        v___y_3843_,
                        v___y_3844_,
                    );
                if leanh::lean_obj_tag(v___x_3849_) == 0 {
                    v_a_3850_ = leanh::lean_ctor_get(v___x_3849_, 0);
                    v_isSharedCheck_3857_ = (!leanh::lean_is_exclusive(v___x_3849_)) as u8;
                    if v_isSharedCheck_3857_ == 0 {
                        v___x_3852_ = v___x_3849_;
                        v_isShared_3853_ = v_isSharedCheck_3857_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3850_);
                        leanh::lean_dec(v___x_3849_);
                        v___x_3852_ = leanh::lean_box(0);
                        v_isShared_3853_ = v_isSharedCheck_3857_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3858_ = leanh::lean_ctor_get(v___x_3849_, 0);
                    v_isSharedCheck_3865_ = (!leanh::lean_is_exclusive(v___x_3849_)) as u8;
                    if v_isSharedCheck_3865_ == 0 {
                        v___x_3860_ = v___x_3849_;
                        v_isShared_3861_ = v_isSharedCheck_3865_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3858_);
                        leanh::lean_dec(v___x_3849_);
                        v___x_3860_ = leanh::lean_box(0);
                        v_isShared_3861_ = v_isSharedCheck_3865_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3853_ == 0 {
                    v___x_3855_ = v___x_3852_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3856_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_a_3850_);
                    v___x_3855_ = v_reuseFailAlloc_3856_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3855_;
            }
            3 => {
                if v_isShared_3861_ == 0 {
                    v___x_3863_ = v___x_3860_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3864_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_a_3858_);
                    v___x_3863_ = v_reuseFailAlloc_3864_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3863_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg___boxed(
    mut v_type_3866_: *mut leanh::LeanObject,
    mut v_k_3867_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_3868_: *mut leanh::LeanObject,
    mut v___y_3869_: *mut leanh::LeanObject,
    mut v___y_3870_: *mut leanh::LeanObject,
    mut v___y_3871_: *mut leanh::LeanObject,
    mut v___y_3872_: *mut leanh::LeanObject,
    mut v___y_3873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_3874_: u8 = 0;
    let mut v_res_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3874_ = (leanh::lean_unbox(v_cleanupAnnotations_3868_) as u8);
    v_res_3875_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_3866_, v_k_3867_, v_cleanupAnnotations_boxed_3874_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
    leanh::lean_dec(v___y_3872_);
    leanh::lean_dec_ref(v___y_3871_);
    leanh::lean_dec(v___y_3870_);
    leanh::lean_dec_ref(v___y_3869_);
    return v_res_3875_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4(
    mut v_00_u03b1_3876_: *mut leanh::LeanObject,
    mut v_type_3877_: *mut leanh::LeanObject,
    mut v_k_3878_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_3879_: u8,
    mut v___y_3880_: *mut leanh::LeanObject,
    mut v___y_3881_: *mut leanh::LeanObject,
    mut v___y_3882_: *mut leanh::LeanObject,
    mut v___y_3883_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3885_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_3877_, v_k_3878_, v_cleanupAnnotations_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_);
    return v___x_3885_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___boxed(
    mut v_00_u03b1_3886_: *mut leanh::LeanObject,
    mut v_type_3887_: *mut leanh::LeanObject,
    mut v_k_3888_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_3889_: *mut leanh::LeanObject,
    mut v___y_3890_: *mut leanh::LeanObject,
    mut v___y_3891_: *mut leanh::LeanObject,
    mut v___y_3892_: *mut leanh::LeanObject,
    mut v___y_3893_: *mut leanh::LeanObject,
    mut v___y_3894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_3895_: u8 = 0;
    let mut v_res_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3895_ = (leanh::lean_unbox(v_cleanupAnnotations_3889_) as u8);
    v_res_3896_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4(v_00_u03b1_3886_, v_type_3887_, v_k_3888_, v_cleanupAnnotations_boxed_3895_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
    leanh::lean_dec(v___y_3893_);
    leanh::lean_dec_ref(v___y_3892_);
    leanh::lean_dec(v___y_3891_);
    leanh::lean_dec_ref(v___y_3890_);
    return v_res_3896_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(
    mut v_name_3897_: *mut leanh::LeanObject,
    mut v_levelParams_3898_: *mut leanh::LeanObject,
    mut v_type_3899_: *mut leanh::LeanObject,
    mut v_value_3900_: *mut leanh::LeanObject,
    mut v_hints_3901_: *mut leanh::LeanObject,
    mut v___y_3902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3906_: u8 = 0;
    let mut v___x_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3913_: u8 = 0;
    let mut v___x_3914_: u8 = 0;
    let mut v___x_3915_: u8 = 0;
    let mut v_env_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: u8 = 0;
    let mut v___x_3918_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3904_ = lean_st_ref_get(v___y_3902_);
                v_env_3916_ = leanh::lean_ctor_get(v___x_3904_, 0);
                leanh::lean_inc_ref_n(v_env_3916_, 2);
                leanh::lean_dec(v___x_3904_);
                v___x_3917_ = l_Lean_Environment_hasUnsafe(v_env_3916_, v_type_3899_);
                if v___x_3917_ == 0 {
                    v___x_3918_ = l_Lean_Environment_hasUnsafe(v_env_3916_, v_value_3900_);
                    v___y_3913_ = v___x_3918_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_env_3916_);
                    v___y_3913_ = v___x_3917_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_name_3897_);
                v___x_3907_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3907_, 0, v_name_3897_);
                leanh::lean_ctor_set(v___x_3907_, 1, v_levelParams_3898_);
                leanh::lean_ctor_set(v___x_3907_, 2, v_type_3899_);
                v___x_3908_ = leanh::lean_box(0);
                v___x_3909_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3909_, 0, v_name_3897_);
                leanh::lean_ctor_set(v___x_3909_, 1, v___x_3908_);
                v___x_3910_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                leanh::lean_ctor_set(v___x_3910_, 0, v___x_3907_);
                leanh::lean_ctor_set(v___x_3910_, 1, v_value_3900_);
                leanh::lean_ctor_set(v___x_3910_, 2, v_hints_3901_);
                leanh::lean_ctor_set(v___x_3910_, 3, v___x_3909_);
                leanh::lean_ctor_set_uint8(
                    v___x_3910_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v___y_3906_,
                );
                v___x_3911_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3911_, 0, v___x_3910_);
                return v___x_3911_;
            }
            2 => {
                if v___y_3913_ == 0 {
                    v___x_3914_ = 1;
                    v___y_3906_ = v___x_3914_;
                    state = 1;
                    continue;
                } else {
                    v___x_3915_ = 0;
                    v___y_3906_ = v___x_3915_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg___boxed(
    mut v_name_3919_: *mut leanh::LeanObject,
    mut v_levelParams_3920_: *mut leanh::LeanObject,
    mut v_type_3921_: *mut leanh::LeanObject,
    mut v_value_3922_: *mut leanh::LeanObject,
    mut v_hints_3923_: *mut leanh::LeanObject,
    mut v___y_3924_: *mut leanh::LeanObject,
    mut v___y_3925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3926_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v_name_3919_, v_levelParams_3920_, v_type_3921_, v_value_3922_, v_hints_3923_, v___y_3924_);
    leanh::lean_dec(v___y_3924_);
    return v_res_3926_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5(
    mut v_name_3927_: *mut leanh::LeanObject,
    mut v_levelParams_3928_: *mut leanh::LeanObject,
    mut v_type_3929_: *mut leanh::LeanObject,
    mut v_value_3930_: *mut leanh::LeanObject,
    mut v_hints_3931_: *mut leanh::LeanObject,
    mut v___y_3932_: *mut leanh::LeanObject,
    mut v___y_3933_: *mut leanh::LeanObject,
    mut v___y_3934_: *mut leanh::LeanObject,
    mut v___y_3935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3937_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v_name_3927_, v_levelParams_3928_, v_type_3929_, v_value_3930_, v_hints_3931_, v___y_3935_);
    return v___x_3937_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___boxed(
    mut v_name_3938_: *mut leanh::LeanObject,
    mut v_levelParams_3939_: *mut leanh::LeanObject,
    mut v_type_3940_: *mut leanh::LeanObject,
    mut v_value_3941_: *mut leanh::LeanObject,
    mut v_hints_3942_: *mut leanh::LeanObject,
    mut v___y_3943_: *mut leanh::LeanObject,
    mut v___y_3944_: *mut leanh::LeanObject,
    mut v___y_3945_: *mut leanh::LeanObject,
    mut v___y_3946_: *mut leanh::LeanObject,
    mut v___y_3947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3948_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5(v_name_3938_, v_levelParams_3939_, v_type_3940_, v_value_3941_, v_hints_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_);
    leanh::lean_dec(v___y_3946_);
    leanh::lean_dec_ref(v___y_3945_);
    leanh::lean_dec(v___y_3944_);
    leanh::lean_dec_ref(v___y_3943_);
    return v_res_3948_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(
    mut v_msg_3949_: *mut leanh::LeanObject,
    mut v___y_3950_: *mut leanh::LeanObject,
    mut v___y_3951_: *mut leanh::LeanObject,
    mut v___y_3952_: *mut leanh::LeanObject,
    mut v___y_3953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200__overap_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3955_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels_spec__0___closed__0;
    v___x_4200__overap_3956_ = lean_panic_fn_borrowed(v___f_3955_, v_msg_3949_);
    leanh::lean_inc(v___y_3953_);
    leanh::lean_inc_ref(v___y_3952_);
    leanh::lean_inc(v___y_3951_);
    leanh::lean_inc_ref(v___y_3950_);
    v___x_3957_ = leanh::lean_apply_5(
        v___x_4200__overap_3956_,
        v___y_3950_,
        v___y_3951_,
        v___y_3952_,
        v___y_3953_,
        leanh::lean_box(0),
    );
    return v___x_3957_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7___boxed(
    mut v_msg_3958_: *mut leanh::LeanObject,
    mut v___y_3959_: *mut leanh::LeanObject,
    mut v___y_3960_: *mut leanh::LeanObject,
    mut v___y_3961_: *mut leanh::LeanObject,
    mut v___y_3962_: *mut leanh::LeanObject,
    mut v___y_3963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3964_ =
        l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(
            v_msg_3958_,
            v___y_3959_,
            v___y_3960_,
            v___y_3961_,
            v___y_3962_,
        );
    leanh::lean_dec(v___y_3962_);
    leanh::lean_dec_ref(v___y_3961_);
    leanh::lean_dec(v___y_3960_);
    leanh::lean_dec_ref(v___y_3959_);
    return v_res_3964_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2(
    mut v_sz_3965_: usize,
    mut v_i_3966_: usize,
    mut v_bs_3967_: *mut leanh::LeanObject,
    mut v___y_3968_: *mut leanh::LeanObject,
    mut v___y_3969_: *mut leanh::LeanObject,
    mut v___y_3970_: *mut leanh::LeanObject,
    mut v___y_3971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3973_: u8 = 0;
    let mut v___x_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: usize = 0;
    let mut v___x_3981_: usize = 0;
    let mut v___x_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3987_: u8 = 0;
    let mut v___x_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3991_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3973_ = lean_usize_dec_lt(v_i_3966_, v_sz_3965_);
                if v___x_3973_ == 0 {
                    v___x_3974_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3974_, 0, v_bs_3967_);
                    return v___x_3974_;
                } else {
                    v_v_3975_ = lean_array_uget_borrowed(v_bs_3967_, v_i_3966_);
                    leanh::lean_inc(v___y_3971_);
                    leanh::lean_inc_ref(v___y_3970_);
                    leanh::lean_inc(v___y_3969_);
                    leanh::lean_inc_ref(v___y_3968_);
                    leanh::lean_inc(v_v_3975_);
                    v___x_3976_ = lean_infer_type(
                        v_v_3975_,
                        v___y_3968_,
                        v___y_3969_,
                        v___y_3970_,
                        v___y_3971_,
                    );
                    if leanh::lean_obj_tag(v___x_3976_) == 0 {
                        v_a_3977_ = leanh::lean_ctor_get(v___x_3976_, 0);
                        leanh::lean_inc(v_a_3977_);
                        leanh::lean_dec_ref_known(v___x_3976_, 1);
                        v___x_3978_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_3979_ = lean_array_uset(v_bs_3967_, v_i_3966_, v___x_3978_);
                        v___x_3980_ = 1usize;
                        v___x_3981_ = lean_usize_add(v_i_3966_, v___x_3980_);
                        v___x_3982_ = lean_array_uset(v_bs_x27_3979_, v_i_3966_, v_a_3977_);
                        v_i_3966_ = v___x_3981_;
                        v_bs_3967_ = v___x_3982_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_3967_);
                        v_a_3984_ = leanh::lean_ctor_get(v___x_3976_, 0);
                        v_isSharedCheck_3991_ =
                            (!leanh::lean_is_exclusive(v___x_3976_)) as u8;
                        if v_isSharedCheck_3991_ == 0 {
                            v___x_3986_ = v___x_3976_;
                            v_isShared_3987_ = v_isSharedCheck_3991_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3984_);
                            leanh::lean_dec(v___x_3976_);
                            v___x_3986_ = leanh::lean_box(0);
                            v_isShared_3987_ = v_isSharedCheck_3991_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3987_ == 0 {
                    v___x_3989_ = v___x_3986_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3990_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3990_, 0, v_a_3984_);
                    v___x_3989_ = v_reuseFailAlloc_3990_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3989_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2___boxed(
    mut v_sz_3992_: *mut leanh::LeanObject,
    mut v_i_3993_: *mut leanh::LeanObject,
    mut v_bs_3994_: *mut leanh::LeanObject,
    mut v___y_3995_: *mut leanh::LeanObject,
    mut v___y_3996_: *mut leanh::LeanObject,
    mut v___y_3997_: *mut leanh::LeanObject,
    mut v___y_3998_: *mut leanh::LeanObject,
    mut v___y_3999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4000_: usize = 0;
    let mut v_i_boxed_4001_: usize = 0;
    let mut v_res_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4000_ = leanh::lean_unbox_usize(v_sz_3992_);
    leanh::lean_dec(v_sz_3992_);
    v_i_boxed_4001_ = leanh::lean_unbox_usize(v_i_3993_);
    leanh::lean_dec(v_i_3993_);
    v_res_4002_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2(v_sz_boxed_4000_, v_i_boxed_4001_, v_bs_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_);
    leanh::lean_dec(v___y_3998_);
    leanh::lean_dec_ref(v___y_3997_);
    leanh::lean_dec(v___y_3996_);
    leanh::lean_dec_ref(v___y_3995_);
    return v_res_4002_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__0(
    mut v___x_4003_: *mut leanh::LeanObject,
    mut v___x_4004_: *mut leanh::LeanObject,
    mut v___x_4005_: *mut leanh::LeanObject,
    mut v___x_4006_: u8,
    mut v_ctorIdx_4007_: *mut leanh::LeanObject,
    mut v___y_4008_: *mut leanh::LeanObject,
    mut v___y_4009_: *mut leanh::LeanObject,
    mut v___y_4010_: *mut leanh::LeanObject,
    mut v___y_4011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_4013_: usize = 0;
    let mut v___x_4014_: usize = 0;
    let mut v___x_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: u8 = 0;
    let mut v___x_4025_: u8 = 0;
    let mut v___x_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4030_: u8 = 0;
    let mut v___x_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4034_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_4013_ = lean_array_size(v___x_4003_);
                v___x_4014_ = 0usize;
                v___x_4015_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__2(v_sz_4013_, v___x_4014_, v___x_4003_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_);
                if leanh::lean_obj_tag(v___x_4015_) == 0 {
                    v_a_4016_ = leanh::lean_ctor_get(v___x_4015_, 0);
                    leanh::lean_inc(v_a_4016_);
                    leanh::lean_dec_ref_known(v___x_4015_, 1);
                    leanh::lean_inc_ref(v_ctorIdx_4007_);
                    v___x_4017_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkNatLookupTableLifting(v_ctorIdx_4007_, v_a_4016_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_);
                    if leanh::lean_obj_tag(v___x_4017_) == 0 {
                        v_a_4018_ = leanh::lean_ctor_get(v___x_4017_, 0);
                        leanh::lean_inc(v_a_4018_);
                        leanh::lean_dec_ref_known(v___x_4017_, 1);
                        v___x_4019_ = leanh::lean_unsigned_to_nat(2);
                        v___x_4020_ = lean_mk_empty_array_with_capacity(v___x_4019_);
                        v___x_4021_ = lean_array_push(v___x_4020_, v___x_4004_);
                        v___x_4022_ = lean_array_push(v___x_4021_, v_ctorIdx_4007_);
                        v___x_4023_ = l_Array_append___redArg(v___x_4005_, v___x_4022_);
                        leanh::lean_dec_ref(v___x_4022_);
                        v___x_4024_ = 1;
                        v___x_4025_ = 1;
                        v___x_4026_ = l_Lean_Meta_mkLambdaFVars(
                            v___x_4023_,
                            v_a_4018_,
                            v___x_4006_,
                            v___x_4024_,
                            v___x_4006_,
                            v___x_4024_,
                            v___x_4025_,
                            v___y_4008_,
                            v___y_4009_,
                            v___y_4010_,
                            v___y_4011_,
                        );
                        leanh::lean_dec_ref(v___x_4023_);
                        return v___x_4026_;
                    } else {
                        leanh::lean_dec_ref(v_ctorIdx_4007_);
                        leanh::lean_dec_ref(v___x_4005_);
                        leanh::lean_dec_ref(v___x_4004_);
                        return v___x_4017_;
                    }
                } else {
                    leanh::lean_dec_ref(v_ctorIdx_4007_);
                    leanh::lean_dec_ref(v___x_4005_);
                    leanh::lean_dec_ref(v___x_4004_);
                    v_a_4027_ = leanh::lean_ctor_get(v___x_4015_, 0);
                    v_isSharedCheck_4034_ = (!leanh::lean_is_exclusive(v___x_4015_)) as u8;
                    if v_isSharedCheck_4034_ == 0 {
                        v___x_4029_ = v___x_4015_;
                        v_isShared_4030_ = v_isSharedCheck_4034_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4027_);
                        leanh::lean_dec(v___x_4015_);
                        v___x_4029_ = leanh::lean_box(0);
                        v_isShared_4030_ = v_isSharedCheck_4034_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4030_ == 0 {
                    v___x_4032_ = v___x_4029_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4033_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4033_, 0, v_a_4027_);
                    v___x_4032_ = v_reuseFailAlloc_4033_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4032_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__0___boxed(
    mut v___x_4035_: *mut leanh::LeanObject,
    mut v___x_4036_: *mut leanh::LeanObject,
    mut v___x_4037_: *mut leanh::LeanObject,
    mut v___x_4038_: *mut leanh::LeanObject,
    mut v_ctorIdx_4039_: *mut leanh::LeanObject,
    mut v___y_4040_: *mut leanh::LeanObject,
    mut v___y_4041_: *mut leanh::LeanObject,
    mut v___y_4042_: *mut leanh::LeanObject,
    mut v___y_4043_: *mut leanh::LeanObject,
    mut v___y_4044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6819__boxed_4045_: u8 = 0;
    let mut v_res_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6819__boxed_4045_ = (leanh::lean_unbox(v___x_4038_) as u8);
    v_res_4046_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__0(
        v___x_4035_,
        v___x_4036_,
        v___x_4037_,
        v___x_6819__boxed_4045_,
        v_ctorIdx_4039_,
        v___y_4040_,
        v___y_4041_,
        v___y_4042_,
        v___y_4043_,
    );
    leanh::lean_dec(v___y_4043_);
    leanh::lean_dec_ref(v___y_4042_);
    leanh::lean_dec(v___y_4041_);
    leanh::lean_dec_ref(v___y_4040_);
    return v_res_4046_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_spec__4___redArg___lam__0(
    mut v_k_4047_: *mut leanh::LeanObject,
    mut v_b_4048_: *mut leanh::LeanObject,
    mut v___y_4049_: *mut leanh::LeanObject,
    mut v___y_4050_: *mut leanh::LeanObject,
    mut v___y_4051_: *mut leanh::LeanObject,
    mut v___y_4052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_4052_);
    leanh::lean_inc_ref(v___y_4051_);
    leanh::lean_inc(v___y_4050_);
    leanh::lean_inc_ref(v___y_4049_);
    v___x_4054_ = leanh::lean_apply_6(
        v_k_4047_,
        v_b_4048_,
        v___y_4049_,
        v___y_4050_,
        v___y_4051_,
        v___y_4052_,
        leanh::lean_box(0),
    );
    return v___x_4054_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_spec__4___redArg___lam__0___boxed(
    mut v_k_4055_: *mut leanh::LeanObject,
    mut v_b_4056_: *mut leanh::LeanObject,
    mut v___y_4057_: *mut leanh::LeanObject,
    mut v___y_4058_: *mut leanh::LeanObject,
    mut v___y_4059_: *mut leanh::LeanObject,
    mut v___y_4060_: *mut leanh::LeanObject,
    mut v___y_4061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4062_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_spec__4___redArg___lam__0(v_k_4055_, v_b_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_);
    leanh::lean_dec(v___y_4060_);
    leanh::lean_dec_ref(v___y_4059_);
    leanh::lean_dec(v___y_4058_);
    leanh::lean_dec_ref(v___y_4057_);
    return v_res_4062_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_spec__4___redArg(
    mut v_name_4063_: *mut leanh::LeanObject,
    mut v_bi_4064_: u8,
    mut v_type_4065_: *mut leanh::LeanObject,
    mut v_k_4066_: *mut leanh::LeanObject,
    mut v_kind_4067_: u8,
    mut v___y_4068_: *mut leanh::LeanObject,
    mut v___y_4069_: *mut leanh::LeanObject,
    mut v___y_4070_: *mut leanh::LeanObject,
    mut v___y_4071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4078_: u8 = 0;
    let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4082_: u8 = 0;
    let mut v_a_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4086_: u8 = 0;
    let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4090_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4073_ = leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_spec__4___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                leanh::lean_closure_set(v___f_4073_, 0, v_k_4066_);
                v___x_4074_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    leanh::lean_box(0),
                    v_name_4063_,
                    v_bi_4064_,
                    v_type_4065_,
                    v___f_4073_,
                    v_kind_4067_,
                    v___y_4068_,
                    v___y_4069_,
                    v___y_4070_,
                    v___y_4071_,
                );
                if leanh::lean_obj_tag(v___x_4074_) == 0 {
                    v_a_4075_ = leanh::lean_ctor_get(v___x_4074_, 0);
                    v_isSharedCheck_4082_ = (!leanh::lean_is_exclusive(v___x_4074_)) as u8;
                    if v_isSharedCheck_4082_ == 0 {
                        v___x_4077_ = v___x_4074_;
                        v_isShared_4078_ = v_isSharedCheck_4082_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4075_);
                        leanh::lean_dec(v___x_4074_);
                        v___x_4077_ = leanh::lean_box(0);
                        v_isShared_4078_ = v_isSharedCheck_4082_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4083_ = leanh::lean_ctor_get(v___x_4074_, 0);
                    v_isSharedCheck_4090_ = (!leanh::lean_is_exclusive(v___x_4074_)) as u8;
                    if v_isSharedCheck_4090_ == 0 {
                        v___x_4085_ = v___x_4074_;
                        v_isShared_4086_ = v_isSharedCheck_4090_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4083_);
                        leanh::lean_dec(v___x_4074_);
                        v___x_4085_ = leanh::lean_box(0);
                        v_isShared_4086_ = v_isSharedCheck_4090_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4078_ == 0 {
                    v___x_4080_ = v___x_4077_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4081_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4081_, 0, v_a_4075_);
                    v___x_4080_ = v_reuseFailAlloc_4081_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4080_;
            }
            3 => {
                if v_isShared_4086_ == 0 {
                    v___x_4088_ = v___x_4085_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4089_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_a_4083_);
                    v___x_4088_ = v_reuseFailAlloc_4089_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4088_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_spec__4___redArg___boxed(
    mut v_name_4091_: *mut leanh::LeanObject,
    mut v_bi_4092_: *mut leanh::LeanObject,
    mut v_type_4093_: *mut leanh::LeanObject,
    mut v_k_4094_: *mut leanh::LeanObject,
    mut v_kind_4095_: *mut leanh::LeanObject,
    mut v___y_4096_: *mut leanh::LeanObject,
    mut v___y_4097_: *mut leanh::LeanObject,
    mut v___y_4098_: *mut leanh::LeanObject,
    mut v___y_4099_: *mut leanh::LeanObject,
    mut v___y_4100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_4101_: u8 = 0;
    let mut v_kind_boxed_4102_: u8 = 0;
    let mut v_res_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_4101_ = (leanh::lean_unbox(v_bi_4092_) as u8);
    v_kind_boxed_4102_ = (leanh::lean_unbox(v_kind_4095_) as u8);
    v_res_4103_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_spec__4___redArg(v_name_4091_, v_bi_boxed_4101_, v_type_4093_, v_k_4094_, v_kind_boxed_4102_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_);
    leanh::lean_dec(v___y_4099_);
    leanh::lean_dec_ref(v___y_4098_);
    leanh::lean_dec(v___y_4097_);
    leanh::lean_dec_ref(v___y_4096_);
    return v_res_4103_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___redArg(
    mut v_name_4104_: *mut leanh::LeanObject,
    mut v_type_4105_: *mut leanh::LeanObject,
    mut v_k_4106_: *mut leanh::LeanObject,
    mut v___y_4107_: *mut leanh::LeanObject,
    mut v___y_4108_: *mut leanh::LeanObject,
    mut v___y_4109_: *mut leanh::LeanObject,
    mut v___y_4110_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4112_: u8 = 0;
    let mut v___x_4113_: u8 = 0;
    let mut v___x_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4112_ = 0;
    v___x_4113_ = 0;
    v___x_4114_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_spec__4___redArg(v_name_4104_, v___x_4112_, v_type_4105_, v_k_4106_, v___x_4113_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_);
    return v___x_4114_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___redArg___boxed(
    mut v_name_4115_: *mut leanh::LeanObject,
    mut v_type_4116_: *mut leanh::LeanObject,
    mut v_k_4117_: *mut leanh::LeanObject,
    mut v___y_4118_: *mut leanh::LeanObject,
    mut v___y_4119_: *mut leanh::LeanObject,
    mut v___y_4120_: *mut leanh::LeanObject,
    mut v___y_4121_: *mut leanh::LeanObject,
    mut v___y_4122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4123_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___redArg(v_name_4115_, v_type_4116_, v_k_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_);
    leanh::lean_dec(v___y_4121_);
    leanh::lean_dec_ref(v___y_4120_);
    leanh::lean_dec(v___y_4119_);
    leanh::lean_dec_ref(v___y_4118_);
    return v_res_4123_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4130_ = leanh::lean_box(0);
    v___x_4131_ =
        l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__3;
    v___x_4132_ = l_Lean_mkConst(v___x_4131_, v___x_4130_);
    return v___x_4132_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1(
    mut v_val_4133_: *mut leanh::LeanObject,
    mut v___x_4134_: *mut leanh::LeanObject,
    mut v___x_4135_: u8,
    mut v_xs_4136_: *mut leanh::LeanObject,
    mut v_x_4137_: *mut leanh::LeanObject,
    mut v___y_4138_: *mut leanh::LeanObject,
    mut v___y_4139_: *mut leanh::LeanObject,
    mut v___y_4140_: *mut leanh::LeanObject,
    mut v___y_4141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_numParams_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_numParams_4143_ = leanh::lean_ctor_get(v_val_4133_, 1);
    leanh::lean_inc_n(v_numParams_4143_, 2);
    v_numIndices_4144_ = leanh::lean_ctor_get(v_val_4133_, 2);
    leanh::lean_inc(v_numIndices_4144_);
    leanh::lean_dec_ref(v_val_4133_);
    leanh::lean_inc_ref(v_xs_4136_);
    v___x_4145_ = l_Array_toSubarray___redArg(v_xs_4136_, v___x_4134_, v_numParams_4143_);
    v___x_4146_ = l_Subarray_copy___redArg(v___x_4145_);
    v___x_4147_ = l_Lean_instInhabitedExpr;
    v___x_4148_ = lean_array_get(v___x_4147_, v_xs_4136_, v_numParams_4143_);
    v___x_4149_ = leanh::lean_unsigned_to_nat(1);
    v___x_4150_ = lean_nat_add(v_numParams_4143_, v___x_4149_);
    leanh::lean_dec(v_numParams_4143_);
    v___x_4151_ = lean_nat_add(v___x_4150_, v_numIndices_4144_);
    leanh::lean_dec(v_numIndices_4144_);
    leanh::lean_dec(v___x_4150_);
    v___x_4152_ = lean_nat_add(v___x_4151_, v___x_4149_);
    leanh::lean_dec(v___x_4151_);
    v___x_4153_ = lean_array_get_size(v_xs_4136_);
    v___x_4154_ = l_Array_toSubarray___redArg(v_xs_4136_, v___x_4152_, v___x_4153_);
    v___x_4155_ = l_Subarray_copy___redArg(v___x_4154_);
    v___x_4156_ = leanh::lean_box((v___x_4135_) as usize);
    v___f_4157_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__0___boxed
            as *mut core::ffi::c_void,
        10,
        4,
    );
    leanh::lean_closure_set(v___f_4157_, 0, v___x_4155_);
    leanh::lean_closure_set(v___f_4157_, 1, v___x_4148_);
    leanh::lean_closure_set(v___f_4157_, 2, v___x_4146_);
    leanh::lean_closure_set(v___f_4157_, 3, v___x_4156_);
    v___x_4158_ =
        l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__1;
    v___x_4159_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4_once), _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4);
    v___x_4160_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___redArg(v___x_4158_, v___x_4159_, v___f_4157_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_);
    return v___x_4160_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___boxed(
    mut v_val_4161_: *mut leanh::LeanObject,
    mut v___x_4162_: *mut leanh::LeanObject,
    mut v___x_4163_: *mut leanh::LeanObject,
    mut v_xs_4164_: *mut leanh::LeanObject,
    mut v_x_4165_: *mut leanh::LeanObject,
    mut v___y_4166_: *mut leanh::LeanObject,
    mut v___y_4167_: *mut leanh::LeanObject,
    mut v___y_4168_: *mut leanh::LeanObject,
    mut v___y_4169_: *mut leanh::LeanObject,
    mut v___y_4170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6995__boxed_4171_: u8 = 0;
    let mut v_res_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6995__boxed_4171_ = (leanh::lean_unbox(v___x_4163_) as u8);
    v_res_4172_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1(
        v_val_4161_,
        v___x_4162_,
        v___x_6995__boxed_4171_,
        v_xs_4164_,
        v_x_4165_,
        v___y_4166_,
        v___y_4167_,
        v___y_4168_,
        v___y_4169_,
    );
    leanh::lean_dec(v___y_4169_);
    leanh::lean_dec_ref(v___y_4168_);
    leanh::lean_dec(v___y_4167_);
    leanh::lean_dec_ref(v___y_4166_);
    leanh::lean_dec_ref(v_x_4165_);
    return v_res_4172_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(
    mut v_ref_4173_: *mut leanh::LeanObject,
    mut v_msg_4174_: *mut leanh::LeanObject,
    mut v___y_4175_: *mut leanh::LeanObject,
    mut v___y_4176_: *mut leanh::LeanObject,
    mut v___y_4177_: *mut leanh::LeanObject,
    mut v___y_4178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4192_: u8 = 0;
    let mut v_cancelTk_x3f_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4194_: u8 = 0;
    let mut v_inheritedTraceOptions_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_4180_ = leanh::lean_ctor_get(v___y_4177_, 0);
    v_fileMap_4181_ = leanh::lean_ctor_get(v___y_4177_, 1);
    v_options_4182_ = leanh::lean_ctor_get(v___y_4177_, 2);
    v_currRecDepth_4183_ = leanh::lean_ctor_get(v___y_4177_, 3);
    v_maxRecDepth_4184_ = leanh::lean_ctor_get(v___y_4177_, 4);
    v_ref_4185_ = leanh::lean_ctor_get(v___y_4177_, 5);
    v_currNamespace_4186_ = leanh::lean_ctor_get(v___y_4177_, 6);
    v_openDecls_4187_ = leanh::lean_ctor_get(v___y_4177_, 7);
    v_initHeartbeats_4188_ = leanh::lean_ctor_get(v___y_4177_, 8);
    v_maxHeartbeats_4189_ = leanh::lean_ctor_get(v___y_4177_, 9);
    v_quotContext_4190_ = leanh::lean_ctor_get(v___y_4177_, 10);
    v_currMacroScope_4191_ = leanh::lean_ctor_get(v___y_4177_, 11);
    v_diag_4192_ = leanh::lean_ctor_get_uint8(
        v___y_4177_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_4193_ = leanh::lean_ctor_get(v___y_4177_, 12);
    v_suppressElabErrors_4194_ = leanh::lean_ctor_get_uint8(
        v___y_4177_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_4195_ = leanh::lean_ctor_get(v___y_4177_, 13);
    v_ref_4196_ = l_Lean_replaceRef(v_ref_4173_, v_ref_4185_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_4195_);
    leanh::lean_inc(v_cancelTk_x3f_4193_);
    leanh::lean_inc(v_currMacroScope_4191_);
    leanh::lean_inc(v_quotContext_4190_);
    leanh::lean_inc(v_maxHeartbeats_4189_);
    leanh::lean_inc(v_initHeartbeats_4188_);
    leanh::lean_inc(v_openDecls_4187_);
    leanh::lean_inc(v_currNamespace_4186_);
    leanh::lean_inc(v_maxRecDepth_4184_);
    leanh::lean_inc(v_currRecDepth_4183_);
    leanh::lean_inc_ref(v_options_4182_);
    leanh::lean_inc_ref(v_fileMap_4181_);
    leanh::lean_inc_ref(v_fileName_4180_);
    v___x_4197_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_4197_, 0, v_fileName_4180_);
    leanh::lean_ctor_set(v___x_4197_, 1, v_fileMap_4181_);
    leanh::lean_ctor_set(v___x_4197_, 2, v_options_4182_);
    leanh::lean_ctor_set(v___x_4197_, 3, v_currRecDepth_4183_);
    leanh::lean_ctor_set(v___x_4197_, 4, v_maxRecDepth_4184_);
    leanh::lean_ctor_set(v___x_4197_, 5, v_ref_4196_);
    leanh::lean_ctor_set(v___x_4197_, 6, v_currNamespace_4186_);
    leanh::lean_ctor_set(v___x_4197_, 7, v_openDecls_4187_);
    leanh::lean_ctor_set(v___x_4197_, 8, v_initHeartbeats_4188_);
    leanh::lean_ctor_set(v___x_4197_, 9, v_maxHeartbeats_4189_);
    leanh::lean_ctor_set(v___x_4197_, 10, v_quotContext_4190_);
    leanh::lean_ctor_set(v___x_4197_, 11, v_currMacroScope_4191_);
    leanh::lean_ctor_set(v___x_4197_, 12, v_cancelTk_x3f_4193_);
    leanh::lean_ctor_set(v___x_4197_, 13, v_inheritedTraceOptions_4195_);
    leanh::lean_ctor_set_uint8(
        v___x_4197_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_4192_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_4197_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_4194_,
    );
    v___x_4198_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v_msg_4174_, v___y_4175_, v___y_4176_, v___x_4197_, v___y_4178_);
    leanh::lean_dec_ref_known(v___x_4197_, 14);
    return v___x_4198_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg___boxed(
    mut v_ref_4199_: *mut leanh::LeanObject,
    mut v_msg_4200_: *mut leanh::LeanObject,
    mut v___y_4201_: *mut leanh::LeanObject,
    mut v___y_4202_: *mut leanh::LeanObject,
    mut v___y_4203_: *mut leanh::LeanObject,
    mut v___y_4204_: *mut leanh::LeanObject,
    mut v___y_4205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4206_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_4199_, v_msg_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_);
    leanh::lean_dec(v___y_4204_);
    leanh::lean_dec_ref(v___y_4203_);
    leanh::lean_dec(v___y_4202_);
    leanh::lean_dec_ref(v___y_4201_);
    leanh::lean_dec(v_ref_4199_);
    return v_res_4206_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4207_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4207_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4208_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__0);
    v___x_4209_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4209_, 0, v___x_4208_);
    return v___x_4209_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4210_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
    v___x_4211_ = leanh::lean_unsigned_to_nat(0);
    v___x_4212_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_4212_, 0, v___x_4211_);
    leanh::lean_ctor_set(v___x_4212_, 1, v___x_4211_);
    leanh::lean_ctor_set(v___x_4212_, 2, v___x_4211_);
    leanh::lean_ctor_set(v___x_4212_, 3, v___x_4211_);
    leanh::lean_ctor_set(v___x_4212_, 4, v___x_4210_);
    leanh::lean_ctor_set(v___x_4212_, 5, v___x_4210_);
    leanh::lean_ctor_set(v___x_4212_, 6, v___x_4210_);
    leanh::lean_ctor_set(v___x_4212_, 7, v___x_4210_);
    leanh::lean_ctor_set(v___x_4212_, 8, v___x_4210_);
    leanh::lean_ctor_set(v___x_4212_, 9, v___x_4210_);
    return v___x_4212_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4213_ = leanh::lean_unsigned_to_nat(32);
    v___x_4214_ = lean_mk_empty_array_with_capacity(v___x_4213_);
    v___x_4215_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4215_, 0, v___x_4214_);
    return v___x_4215_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4216_: usize = 0;
    let mut v___x_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4216_ = 5usize;
    v___x_4217_ = leanh::lean_unsigned_to_nat(0);
    v___x_4218_ = leanh::lean_unsigned_to_nat(32);
    v___x_4219_ = lean_mk_empty_array_with_capacity(v___x_4218_);
    v___x_4220_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3);
    v___x_4221_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_4221_, 0, v___x_4220_);
    leanh::lean_ctor_set(v___x_4221_, 1, v___x_4219_);
    leanh::lean_ctor_set(v___x_4221_, 2, v___x_4217_);
    leanh::lean_ctor_set(v___x_4221_, 3, v___x_4217_);
    leanh::lean_ctor_set_usize(v___x_4221_, 4, v___x_4216_);
    return v___x_4221_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4222_ = leanh::lean_box(1);
    v___x_4223_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__4);
    v___x_4224_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__1);
    v___x_4225_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4225_, 0, v___x_4224_);
    leanh::lean_ctor_set(v___x_4225_, 1, v___x_4223_);
    leanh::lean_ctor_set(v___x_4225_, 2, v___x_4222_);
    return v___x_4225_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4227_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__6;
    v___x_4228_ = l_Lean_stringToMessageData(v___x_4227_);
    return v___x_4228_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4230_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__8;
    v___x_4231_ = l_Lean_stringToMessageData(v___x_4230_);
    return v___x_4231_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4233_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__10;
    v___x_4234_ = l_Lean_stringToMessageData(v___x_4233_);
    return v___x_4234_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4236_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__12;
    v___x_4237_ = l_Lean_stringToMessageData(v___x_4236_);
    return v___x_4237_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4239_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__14;
    v___x_4240_ = l_Lean_stringToMessageData(v___x_4239_);
    return v___x_4240_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4242_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__16;
    v___x_4243_ = l_Lean_stringToMessageData(v___x_4242_);
    return v___x_4243_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4245_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__18;
    v___x_4246_ = l_Lean_stringToMessageData(v___x_4245_);
    return v___x_4246_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(
    mut v_msg_4247_: *mut leanh::LeanObject,
    mut v_declHint_4248_: *mut leanh::LeanObject,
    mut v___y_4249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: u8 = 0;
    let mut v_isExporting_4254_: u8 = 0;
    let mut v___x_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: u8 = 0;
    let mut v___x_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4276_: u8 = 0;
    let mut v___x_4277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: u8 = 0;
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
    let mut v___x_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4308_: u8 = 0;
    let mut v___x_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4251_ = lean_st_ref_get(v___y_4249_);
                v_env_4252_ = leanh::lean_ctor_get(v___x_4251_, 0);
                leanh::lean_inc_ref(v_env_4252_);
                leanh::lean_dec(v___x_4251_);
                v___x_4253_ = l_Lean_Name_isAnonymous(v_declHint_4248_);
                if v___x_4253_ == 0 {
                    v_isExporting_4254_ = leanh::lean_ctor_get_uint8(
                        v_env_4252_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_4254_ == 0 {
                        leanh::lean_dec_ref(v_env_4252_);
                        leanh::lean_dec(v_declHint_4248_);
                        v___x_4255_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4255_, 0, v_msg_4247_);
                        return v___x_4255_;
                    } else {
                        leanh::lean_inc_ref(v_env_4252_);
                        v___x_4256_ = l_Lean_Environment_setExporting(v_env_4252_, v___x_4253_);
                        leanh::lean_inc(v_declHint_4248_);
                        leanh::lean_inc_ref(v___x_4256_);
                        v___x_4257_ = l_Lean_Environment_contains(
                            v___x_4256_,
                            v_declHint_4248_,
                            v_isExporting_4254_,
                        );
                        if v___x_4257_ == 0 {
                            leanh::lean_dec_ref(v___x_4256_);
                            leanh::lean_dec_ref(v_env_4252_);
                            leanh::lean_dec(v_declHint_4248_);
                            v___x_4258_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_4258_, 0, v_msg_4247_);
                            return v___x_4258_;
                        } else {
                            v___x_4259_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2);
                            v___x_4260_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5);
                            v___x_4261_ = l_Lean_Options_empty;
                            v___x_4262_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_4262_, 0, v___x_4256_);
                            leanh::lean_ctor_set(v___x_4262_, 1, v___x_4259_);
                            leanh::lean_ctor_set(v___x_4262_, 2, v___x_4260_);
                            leanh::lean_ctor_set(v___x_4262_, 3, v___x_4261_);
                            leanh::lean_inc(v_declHint_4248_);
                            v___x_4263_ =
                                l_Lean_MessageData_ofConstName(v_declHint_4248_, v___x_4253_);
                            v_c_4264_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_4264_, 0, v___x_4262_);
                            leanh::lean_ctor_set(v_c_4264_, 1, v___x_4263_);
                            v___x_4265_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_4252_,
                                v_declHint_4248_,
                            );
                            if leanh::lean_obj_tag(v___x_4265_) == 0 {
                                leanh::lean_dec_ref(v_env_4252_);
                                leanh::lean_dec(v_declHint_4248_);
                                v___x_4266_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7);
                                v___x_4267_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_4267_, 0, v___x_4266_);
                                leanh::lean_ctor_set(v___x_4267_, 1, v_c_4264_);
                                v___x_4268_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__9);
                                v___x_4269_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_4269_, 0, v___x_4267_);
                                leanh::lean_ctor_set(v___x_4269_, 1, v___x_4268_);
                                v___x_4270_ = l_Lean_MessageData_note(v___x_4269_);
                                v___x_4271_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_4271_, 0, v_msg_4247_);
                                leanh::lean_ctor_set(v___x_4271_, 1, v___x_4270_);
                                v___x_4272_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_4272_, 0, v___x_4271_);
                                return v___x_4272_;
                            } else {
                                v_val_4273_ = leanh::lean_ctor_get(v___x_4265_, 0);
                                v_isSharedCheck_4308_ =
                                    (!leanh::lean_is_exclusive(v___x_4265_)) as u8;
                                if v_isSharedCheck_4308_ == 0 {
                                    v___x_4275_ = v___x_4265_;
                                    v_isShared_4276_ = v_isSharedCheck_4308_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_4273_);
                                    leanh::lean_dec(v___x_4265_);
                                    v___x_4275_ = leanh::lean_box(0);
                                    v_isShared_4276_ = v_isSharedCheck_4308_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_4252_);
                    leanh::lean_dec(v_declHint_4248_);
                    v___x_4309_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4309_, 0, v_msg_4247_);
                    return v___x_4309_;
                }
            }
            1 => {
                v___x_4277_ = leanh::lean_box(0);
                v___x_4278_ = l_Lean_Environment_header(v_env_4252_);
                leanh::lean_dec_ref(v_env_4252_);
                v___x_4279_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4278_);
                v_mod_4280_ = lean_array_get(v___x_4277_, v___x_4279_, v_val_4273_);
                leanh::lean_dec(v_val_4273_);
                leanh::lean_dec_ref(v___x_4279_);
                v___x_4281_ = l_Lean_isPrivateName(v_declHint_4248_);
                leanh::lean_dec(v_declHint_4248_);
                if v___x_4281_ == 0 {
                    v___x_4282_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__11);
                    v___x_4283_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4283_, 0, v___x_4282_);
                    leanh::lean_ctor_set(v___x_4283_, 1, v_c_4264_);
                    v___x_4284_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__13);
                    v___x_4285_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4285_, 0, v___x_4283_);
                    leanh::lean_ctor_set(v___x_4285_, 1, v___x_4284_);
                    v___x_4286_ = l_Lean_MessageData_ofName(v_mod_4280_);
                    v___x_4287_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4287_, 0, v___x_4285_);
                    leanh::lean_ctor_set(v___x_4287_, 1, v___x_4286_);
                    v___x_4288_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__15);
                    v___x_4289_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4289_, 0, v___x_4287_);
                    leanh::lean_ctor_set(v___x_4289_, 1, v___x_4288_);
                    v___x_4290_ = l_Lean_MessageData_note(v___x_4289_);
                    v___x_4291_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4291_, 0, v_msg_4247_);
                    leanh::lean_ctor_set(v___x_4291_, 1, v___x_4290_);
                    if v_isShared_4276_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4275_, 0);
                        leanh::lean_ctor_set(v___x_4275_, 0, v___x_4291_);
                        v___x_4293_ = v___x_4275_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4294_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4294_, 0, v___x_4291_);
                        v___x_4293_ = v_reuseFailAlloc_4294_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4295_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__7);
                    v___x_4296_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4296_, 0, v___x_4295_);
                    leanh::lean_ctor_set(v___x_4296_, 1, v_c_4264_);
                    v___x_4297_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__17);
                    v___x_4298_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4298_, 0, v___x_4296_);
                    leanh::lean_ctor_set(v___x_4298_, 1, v___x_4297_);
                    v___x_4299_ = l_Lean_MessageData_ofName(v_mod_4280_);
                    v___x_4300_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4300_, 0, v___x_4298_);
                    leanh::lean_ctor_set(v___x_4300_, 1, v___x_4299_);
                    v___x_4301_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__19);
                    v___x_4302_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4302_, 0, v___x_4300_);
                    leanh::lean_ctor_set(v___x_4302_, 1, v___x_4301_);
                    v___x_4303_ = l_Lean_MessageData_note(v___x_4302_);
                    v___x_4304_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4304_, 0, v_msg_4247_);
                    leanh::lean_ctor_set(v___x_4304_, 1, v___x_4303_);
                    if v_isShared_4276_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4275_, 0);
                        leanh::lean_ctor_set(v___x_4275_, 0, v___x_4304_);
                        v___x_4306_ = v___x_4275_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4307_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4307_, 0, v___x_4304_);
                        v___x_4306_ = v_reuseFailAlloc_4307_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4293_;
            }
            3 => {
                return v___x_4306_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___boxed(
    mut v_msg_4310_: *mut leanh::LeanObject,
    mut v_declHint_4311_: *mut leanh::LeanObject,
    mut v___y_4312_: *mut leanh::LeanObject,
    mut v___y_4313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4314_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_4310_, v_declHint_4311_, v___y_4312_);
    leanh::lean_dec(v___y_4312_);
    return v_res_4314_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12(
    mut v_msg_4315_: *mut leanh::LeanObject,
    mut v_declHint_4316_: *mut leanh::LeanObject,
    mut v___y_4317_: *mut leanh::LeanObject,
    mut v___y_4318_: *mut leanh::LeanObject,
    mut v___y_4319_: *mut leanh::LeanObject,
    mut v___y_4320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4326_: u8 = 0;
    let mut v___x_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4332_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4322_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_4315_, v_declHint_4316_, v___y_4320_);
                v_a_4323_ = leanh::lean_ctor_get(v___x_4322_, 0);
                v_isSharedCheck_4332_ = (!leanh::lean_is_exclusive(v___x_4322_)) as u8;
                if v_isSharedCheck_4332_ == 0 {
                    v___x_4325_ = v___x_4322_;
                    v_isShared_4326_ = v_isSharedCheck_4332_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4323_);
                    leanh::lean_dec(v___x_4322_);
                    v___x_4325_ = leanh::lean_box(0);
                    v_isShared_4326_ = v_isSharedCheck_4332_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4327_ = l_Lean_unknownIdentifierMessageTag;
                v___x_4328_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4328_, 0, v___x_4327_);
                leanh::lean_ctor_set(v___x_4328_, 1, v_a_4323_);
                if v_isShared_4326_ == 0 {
                    leanh::lean_ctor_set(v___x_4325_, 0, v___x_4328_);
                    v___x_4330_ = v___x_4325_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4331_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4331_, 0, v___x_4328_);
                    v___x_4330_ = v_reuseFailAlloc_4331_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4330_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12___boxed(
    mut v_msg_4333_: *mut leanh::LeanObject,
    mut v_declHint_4334_: *mut leanh::LeanObject,
    mut v___y_4335_: *mut leanh::LeanObject,
    mut v___y_4336_: *mut leanh::LeanObject,
    mut v___y_4337_: *mut leanh::LeanObject,
    mut v___y_4338_: *mut leanh::LeanObject,
    mut v___y_4339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4340_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_4333_, v_declHint_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_);
    leanh::lean_dec(v___y_4338_);
    leanh::lean_dec_ref(v___y_4337_);
    leanh::lean_dec(v___y_4336_);
    leanh::lean_dec_ref(v___y_4335_);
    return v_res_4340_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___redArg(
    mut v_ref_4341_: *mut leanh::LeanObject,
    mut v_msg_4342_: *mut leanh::LeanObject,
    mut v_declHint_4343_: *mut leanh::LeanObject,
    mut v___y_4344_: *mut leanh::LeanObject,
    mut v___y_4345_: *mut leanh::LeanObject,
    mut v___y_4346_: *mut leanh::LeanObject,
    mut v___y_4347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4349_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12(v_msg_4342_, v_declHint_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
    v_a_4350_ = leanh::lean_ctor_get(v___x_4349_, 0);
    leanh::lean_inc(v_a_4350_);
    leanh::lean_dec_ref(v___x_4349_);
    v___x_4351_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_4341_, v_a_4350_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
    return v___x_4351_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___redArg___boxed(
    mut v_ref_4352_: *mut leanh::LeanObject,
    mut v_msg_4353_: *mut leanh::LeanObject,
    mut v_declHint_4354_: *mut leanh::LeanObject,
    mut v___y_4355_: *mut leanh::LeanObject,
    mut v___y_4356_: *mut leanh::LeanObject,
    mut v___y_4357_: *mut leanh::LeanObject,
    mut v___y_4358_: *mut leanh::LeanObject,
    mut v___y_4359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4360_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_4352_, v_msg_4353_, v_declHint_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_);
    leanh::lean_dec(v___y_4358_);
    leanh::lean_dec_ref(v___y_4357_);
    leanh::lean_dec(v___y_4356_);
    leanh::lean_dec_ref(v___y_4355_);
    leanh::lean_dec(v_ref_4352_);
    return v_res_4360_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4362_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__0;
    v___x_4363_ = l_Lean_stringToMessageData(v___x_4362_);
    return v___x_4363_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4365_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__2;
    v___x_4366_ = l_Lean_stringToMessageData(v___x_4365_);
    return v___x_4366_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg(
    mut v_ref_4367_: *mut leanh::LeanObject,
    mut v_constName_4368_: *mut leanh::LeanObject,
    mut v___y_4369_: *mut leanh::LeanObject,
    mut v___y_4370_: *mut leanh::LeanObject,
    mut v___y_4371_: *mut leanh::LeanObject,
    mut v___y_4372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: u8 = 0;
    let mut v___x_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4374_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__1);
    v___x_4375_ = 0;
    leanh::lean_inc(v_constName_4368_);
    v___x_4376_ = l_Lean_MessageData_ofConstName(v_constName_4368_, v___x_4375_);
    v___x_4377_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4377_, 0, v___x_4374_);
    leanh::lean_ctor_set(v___x_4377_, 1, v___x_4376_);
    v___x_4378_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3);
    v___x_4379_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4379_, 0, v___x_4377_);
    leanh::lean_ctor_set(v___x_4379_, 1, v___x_4378_);
    v___x_4380_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_4367_, v___x_4379_, v_constName_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_);
    return v___x_4380_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___boxed(
    mut v_ref_4381_: *mut leanh::LeanObject,
    mut v_constName_4382_: *mut leanh::LeanObject,
    mut v___y_4383_: *mut leanh::LeanObject,
    mut v___y_4384_: *mut leanh::LeanObject,
    mut v___y_4385_: *mut leanh::LeanObject,
    mut v___y_4386_: *mut leanh::LeanObject,
    mut v___y_4387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4388_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg(v_ref_4381_, v_constName_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_);
    leanh::lean_dec(v___y_4386_);
    leanh::lean_dec_ref(v___y_4385_);
    leanh::lean_dec(v___y_4384_);
    leanh::lean_dec_ref(v___y_4383_);
    leanh::lean_dec(v_ref_4381_);
    return v_res_4388_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(
    mut v_constName_4389_: *mut leanh::LeanObject,
    mut v___y_4390_: *mut leanh::LeanObject,
    mut v___y_4391_: *mut leanh::LeanObject,
    mut v___y_4392_: *mut leanh::LeanObject,
    mut v___y_4393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_4395_ = leanh::lean_ctor_get(v___y_4392_, 5);
    v___x_4396_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg(v_ref_4395_, v_constName_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_);
    return v___x_4396_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg___boxed(
    mut v_constName_4397_: *mut leanh::LeanObject,
    mut v___y_4398_: *mut leanh::LeanObject,
    mut v___y_4399_: *mut leanh::LeanObject,
    mut v___y_4400_: *mut leanh::LeanObject,
    mut v___y_4401_: *mut leanh::LeanObject,
    mut v___y_4402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4403_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(v_constName_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_);
    leanh::lean_dec(v___y_4401_);
    leanh::lean_dec_ref(v___y_4400_);
    leanh::lean_dec(v___y_4399_);
    leanh::lean_dec_ref(v___y_4398_);
    return v_res_4403_;
}
pub unsafe fn l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1(
    mut v_constName_4404_: *mut leanh::LeanObject,
    mut v___y_4405_: *mut leanh::LeanObject,
    mut v___y_4406_: *mut leanh::LeanObject,
    mut v___y_4407_: *mut leanh::LeanObject,
    mut v___y_4408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: u8 = 0;
    let mut v___x_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4418_: u8 = 0;
    let mut v___x_4420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4422_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4410_ = lean_st_ref_get(v___y_4408_);
                v_env_4411_ = leanh::lean_ctor_get(v___x_4410_, 0);
                leanh::lean_inc_ref(v_env_4411_);
                leanh::lean_dec(v___x_4410_);
                v___x_4412_ = 0;
                leanh::lean_inc(v_constName_4404_);
                v___x_4413_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_4411_,
                    v_constName_4404_,
                    v___x_4412_,
                );
                if leanh::lean_obj_tag(v___x_4413_) == 0 {
                    v___x_4414_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(v_constName_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_);
                    return v___x_4414_;
                } else {
                    leanh::lean_dec(v_constName_4404_);
                    v_val_4415_ = leanh::lean_ctor_get(v___x_4413_, 0);
                    v_isSharedCheck_4422_ = (!leanh::lean_is_exclusive(v___x_4413_)) as u8;
                    if v_isSharedCheck_4422_ == 0 {
                        v___x_4417_ = v___x_4413_;
                        v_isShared_4418_ = v_isSharedCheck_4422_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4415_);
                        leanh::lean_dec(v___x_4413_);
                        v___x_4417_ = leanh::lean_box(0);
                        v_isShared_4418_ = v_isSharedCheck_4422_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4418_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4417_, 0);
                    v___x_4420_ = v___x_4417_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4421_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_val_4415_);
                    v___x_4420_ = v_reuseFailAlloc_4421_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4420_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1___boxed(
    mut v_constName_4423_: *mut leanh::LeanObject,
    mut v___y_4424_: *mut leanh::LeanObject,
    mut v___y_4425_: *mut leanh::LeanObject,
    mut v___y_4426_: *mut leanh::LeanObject,
    mut v___y_4427_: *mut leanh::LeanObject,
    mut v___y_4428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4429_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1(v_constName_4423_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_);
    leanh::lean_dec(v___y_4427_);
    leanh::lean_dec_ref(v___y_4426_);
    leanh::lean_dec(v___y_4425_);
    leanh::lean_dec_ref(v___y_4424_);
    return v_res_4429_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(
    mut v_constName_4430_: *mut leanh::LeanObject,
    mut v___y_4431_: *mut leanh::LeanObject,
    mut v___y_4432_: *mut leanh::LeanObject,
    mut v___y_4433_: *mut leanh::LeanObject,
    mut v___y_4434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: u8 = 0;
    let mut v___x_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4444_: u8 = 0;
    let mut v___x_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4448_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4436_ = lean_st_ref_get(v___y_4434_);
                v_env_4437_ = leanh::lean_ctor_get(v___x_4436_, 0);
                leanh::lean_inc_ref(v_env_4437_);
                leanh::lean_dec(v___x_4436_);
                v___x_4438_ = 0;
                leanh::lean_inc(v_constName_4430_);
                v___x_4439_ =
                    l_Lean_Environment_find_x3f(v_env_4437_, v_constName_4430_, v___x_4438_);
                if leanh::lean_obj_tag(v___x_4439_) == 0 {
                    v___x_4440_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(v_constName_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_);
                    return v___x_4440_;
                } else {
                    leanh::lean_dec(v_constName_4430_);
                    v_val_4441_ = leanh::lean_ctor_get(v___x_4439_, 0);
                    v_isSharedCheck_4448_ = (!leanh::lean_is_exclusive(v___x_4439_)) as u8;
                    if v_isSharedCheck_4448_ == 0 {
                        v___x_4443_ = v___x_4439_;
                        v_isShared_4444_ = v_isSharedCheck_4448_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4441_);
                        leanh::lean_dec(v___x_4439_);
                        v___x_4443_ = leanh::lean_box(0);
                        v_isShared_4444_ = v_isSharedCheck_4448_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4444_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4443_, 0);
                    v___x_4446_ = v___x_4443_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4447_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4447_, 0, v_val_4441_);
                    v___x_4446_ = v_reuseFailAlloc_4447_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4446_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0___boxed(
    mut v_constName_4449_: *mut leanh::LeanObject,
    mut v___y_4450_: *mut leanh::LeanObject,
    mut v___y_4451_: *mut leanh::LeanObject,
    mut v___y_4452_: *mut leanh::LeanObject,
    mut v___y_4453_: *mut leanh::LeanObject,
    mut v___y_4454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4455_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_constName_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_);
    leanh::lean_dec(v___y_4453_);
    leanh::lean_dec_ref(v___y_4452_);
    leanh::lean_dec(v___y_4451_);
    leanh::lean_dec_ref(v___y_4450_);
    return v_res_4455_;
}
pub unsafe fn _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4456_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4456_;
}
pub unsafe fn _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4457_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__0);
    v___x_4458_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4458_, 0, v___x_4457_);
    return v___x_4458_;
}
pub unsafe fn _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4459_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1);
    v___x_4460_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4460_, 0, v___x_4459_);
    leanh::lean_ctor_set(v___x_4460_, 1, v___x_4459_);
    return v___x_4460_;
}
pub unsafe fn _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4461_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__1);
    v___x_4462_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_4462_, 0, v___x_4461_);
    leanh::lean_ctor_set(v___x_4462_, 1, v___x_4461_);
    leanh::lean_ctor_set(v___x_4462_, 2, v___x_4461_);
    leanh::lean_ctor_set(v___x_4462_, 3, v___x_4461_);
    leanh::lean_ctor_set(v___x_4462_, 4, v___x_4461_);
    leanh::lean_ctor_set(v___x_4462_, 5, v___x_4461_);
    return v___x_4462_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg(
    mut v_declName_4463_: *mut leanh::LeanObject,
    mut v_s_4464_: u8,
    mut v___y_4465_: *mut leanh::LeanObject,
    mut v___y_4466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4479_: u8 = 0;
    let mut v___x_4480_: u8 = 0;
    let mut v___x_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4494_: u8 = 0;
    let mut v___x_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4502_: u8 = 0;
    let mut v_unused_4503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4505_: u8 = 0;
    let mut v_unused_4506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4468_ = lean_st_ref_take(v___y_4466_);
                v_env_4469_ = leanh::lean_ctor_get(v___x_4468_, 0);
                v_nextMacroScope_4470_ = leanh::lean_ctor_get(v___x_4468_, 1);
                v_ngen_4471_ = leanh::lean_ctor_get(v___x_4468_, 2);
                v_auxDeclNGen_4472_ = leanh::lean_ctor_get(v___x_4468_, 3);
                v_traceState_4473_ = leanh::lean_ctor_get(v___x_4468_, 4);
                v_messages_4474_ = leanh::lean_ctor_get(v___x_4468_, 6);
                v_infoState_4475_ = leanh::lean_ctor_get(v___x_4468_, 7);
                v_snapshotTasks_4476_ = leanh::lean_ctor_get(v___x_4468_, 8);
                v_isSharedCheck_4505_ = (!leanh::lean_is_exclusive(v___x_4468_)) as u8;
                if v_isSharedCheck_4505_ == 0 {
                    v_unused_4506_ = leanh::lean_ctor_get(v___x_4468_, 5);
                    leanh::lean_dec(v_unused_4506_);
                    v___x_4478_ = v___x_4468_;
                    v_isShared_4479_ = v_isSharedCheck_4505_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4476_);
                    leanh::lean_inc(v_infoState_4475_);
                    leanh::lean_inc(v_messages_4474_);
                    leanh::lean_inc(v_traceState_4473_);
                    leanh::lean_inc(v_auxDeclNGen_4472_);
                    leanh::lean_inc(v_ngen_4471_);
                    leanh::lean_inc(v_nextMacroScope_4470_);
                    leanh::lean_inc(v_env_4469_);
                    leanh::lean_dec(v___x_4468_);
                    v___x_4478_ = leanh::lean_box(0);
                    v_isShared_4479_ = v_isSharedCheck_4505_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4480_ = 0;
                v___x_4481_ = leanh::lean_box(0);
                v___x_4482_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(
                    v_env_4469_,
                    v_declName_4463_,
                    v_s_4464_,
                    v___x_4480_,
                    v___x_4481_,
                );
                v___x_4483_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2);
                if v_isShared_4479_ == 0 {
                    leanh::lean_ctor_set(v___x_4478_, 5, v___x_4483_);
                    leanh::lean_ctor_set(v___x_4478_, 0, v___x_4482_);
                    v___x_4485_ = v___x_4478_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4504_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4504_, 0, v___x_4482_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4504_, 1, v_nextMacroScope_4470_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4504_, 2, v_ngen_4471_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4504_, 3, v_auxDeclNGen_4472_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4504_, 4, v_traceState_4473_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4504_, 5, v___x_4483_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4504_, 6, v_messages_4474_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4504_, 7, v_infoState_4475_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4504_, 8, v_snapshotTasks_4476_);
                    v___x_4485_ = v_reuseFailAlloc_4504_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4486_ = lean_st_ref_set(v___y_4466_, v___x_4485_);
                v___x_4487_ = lean_st_ref_take(v___y_4465_);
                v_mctx_4488_ = leanh::lean_ctor_get(v___x_4487_, 0);
                v_zetaDeltaFVarIds_4489_ = leanh::lean_ctor_get(v___x_4487_, 2);
                v_postponed_4490_ = leanh::lean_ctor_get(v___x_4487_, 3);
                v_diag_4491_ = leanh::lean_ctor_get(v___x_4487_, 4);
                v_isSharedCheck_4502_ = (!leanh::lean_is_exclusive(v___x_4487_)) as u8;
                if v_isSharedCheck_4502_ == 0 {
                    v_unused_4503_ = leanh::lean_ctor_get(v___x_4487_, 1);
                    leanh::lean_dec(v_unused_4503_);
                    v___x_4493_ = v___x_4487_;
                    v_isShared_4494_ = v_isSharedCheck_4502_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_4491_);
                    leanh::lean_inc(v_postponed_4490_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_4489_);
                    leanh::lean_inc(v_mctx_4488_);
                    leanh::lean_dec(v___x_4487_);
                    v___x_4493_ = leanh::lean_box(0);
                    v_isShared_4494_ = v_isSharedCheck_4502_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4495_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3);
                if v_isShared_4494_ == 0 {
                    leanh::lean_ctor_set(v___x_4493_, 1, v___x_4495_);
                    v___x_4497_ = v___x_4493_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4501_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4501_, 0, v_mctx_4488_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4501_, 1, v___x_4495_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4501_,
                        2,
                        v_zetaDeltaFVarIds_4489_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4501_, 3, v_postponed_4490_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4501_, 4, v_diag_4491_);
                    v___x_4497_ = v_reuseFailAlloc_4501_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4498_ = lean_st_ref_set(v___y_4465_, v___x_4497_);
                v___x_4499_ = leanh::lean_box(0);
                v___x_4500_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4500_, 0, v___x_4499_);
                return v___x_4500_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___boxed(
    mut v_declName_4507_: *mut leanh::LeanObject,
    mut v_s_4508_: *mut leanh::LeanObject,
    mut v___y_4509_: *mut leanh::LeanObject,
    mut v___y_4510_: *mut leanh::LeanObject,
    mut v___y_4511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_boxed_4512_: u8 = 0;
    let mut v_res_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_s_boxed_4512_ = (leanh::lean_unbox(v_s_4508_) as u8);
    v_res_4513_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg(v_declName_4507_, v_s_boxed_4512_, v___y_4509_, v___y_4510_);
    leanh::lean_dec(v___y_4510_);
    leanh::lean_dec(v___y_4509_);
    return v_res_4513_;
}
pub unsafe fn l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(
    mut v_declName_4514_: *mut leanh::LeanObject,
    mut v___y_4515_: *mut leanh::LeanObject,
    mut v___y_4516_: *mut leanh::LeanObject,
    mut v___y_4517_: *mut leanh::LeanObject,
    mut v___y_4518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4520_: u8 = 0;
    let mut v___x_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4520_ = 0;
    v___x_4521_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg(v_declName_4514_, v___x_4520_, v___y_4516_, v___y_4518_);
    return v___x_4521_;
}
pub unsafe fn l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6___boxed(
    mut v_declName_4522_: *mut leanh::LeanObject,
    mut v___y_4523_: *mut leanh::LeanObject,
    mut v___y_4524_: *mut leanh::LeanObject,
    mut v___y_4525_: *mut leanh::LeanObject,
    mut v___y_4526_: *mut leanh::LeanObject,
    mut v___y_4527_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4528_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(v_declName_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
    leanh::lean_dec(v___y_4526_);
    leanh::lean_dec_ref(v___y_4525_);
    leanh::lean_dec(v___y_4524_);
    leanh::lean_dec_ref(v___y_4523_);
    return v_res_4528_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4531_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__1;
    v___x_4532_ = leanh::lean_unsigned_to_nat(60);
    v___x_4533_ = leanh::lean_unsigned_to_nat(81);
    v___x_4534_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__0;
    v___x_4535_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0;
    v___x_4536_ = l_mkPanicMessageWithDecl(
        v___x_4535_,
        v___x_4534_,
        v___x_4533_,
        v___x_4532_,
        v___x_4531_,
    );
    return v___x_4536_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType(
    mut v_indName_4537_: *mut leanh::LeanObject,
    mut v_a_4538_: *mut leanh::LeanObject,
    mut v_a_4539_: *mut leanh::LeanObject,
    mut v_a_4540_: *mut leanh::LeanObject,
    mut v_a_4541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4547_: u8 = 0;
    let mut v_val_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: u8 = 0;
    let mut v___x_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4569_: u8 = 0;
    let mut v___x_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: u8 = 0;
    let mut v___x_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4585_: u8 = 0;
    let mut v___x_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4598_: u8 = 0;
    let mut v___x_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4614_: u8 = 0;
    let mut v___x_4615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4626_: u8 = 0;
    let mut v___x_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4632_: u8 = 0;
    let mut v_unused_4633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4635_: u8 = 0;
    let mut v_unused_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4638_: u8 = 0;
    let mut v_unused_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4641_: u8 = 0;
    let mut v_unused_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4644_: u8 = 0;
    let mut v_a_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4648_: u8 = 0;
    let mut v___x_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4652_: u8 = 0;
    let mut v_a_4653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4656_: u8 = 0;
    let mut v___x_4658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4660_: u8 = 0;
    let mut v_a_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4664_: u8 = 0;
    let mut v___x_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4668_: u8 = 0;
    let mut v___x_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4675_: u8 = 0;
    let mut v_a_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4679_: u8 = 0;
    let mut v___x_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4683_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_indName_4537_);
                v___x_4543_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_indName_4537_, v_a_4538_, v_a_4539_, v_a_4540_, v_a_4541_);
                if leanh::lean_obj_tag(v___x_4543_) == 0 {
                    v_a_4544_ = leanh::lean_ctor_get(v___x_4543_, 0);
                    v_isSharedCheck_4675_ = (!leanh::lean_is_exclusive(v___x_4543_)) as u8;
                    if v_isSharedCheck_4675_ == 0 {
                        v___x_4546_ = v___x_4543_;
                        v_isShared_4547_ = v_isSharedCheck_4675_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4544_);
                        leanh::lean_dec(v___x_4543_);
                        v___x_4546_ = leanh::lean_box(0);
                        v_isShared_4547_ = v_isSharedCheck_4675_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_indName_4537_);
                    v_a_4676_ = leanh::lean_ctor_get(v___x_4543_, 0);
                    v_isSharedCheck_4683_ = (!leanh::lean_is_exclusive(v___x_4543_)) as u8;
                    if v_isSharedCheck_4683_ == 0 {
                        v___x_4678_ = v___x_4543_;
                        v_isShared_4679_ = v_isSharedCheck_4683_;
                        state = 19;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4676_);
                        leanh::lean_dec(v___x_4543_);
                        v___x_4678_ = leanh::lean_box(0);
                        v_isShared_4679_ = v_isSharedCheck_4683_;
                        state = 19;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4544_) == 5 {
                    v_val_4548_ = leanh::lean_ctor_get(v_a_4544_, 0);
                    leanh::lean_inc_ref(v_val_4548_);
                    leanh::lean_dec_ref_known(v_a_4544_, 1);
                    v___x_4549_ = l_Lean_InductiveVal_numCtors(v_val_4548_);
                    v___x_4550_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4551_ = lean_nat_dec_eq(v___x_4549_, v___x_4550_);
                    leanh::lean_dec(v___x_4549_);
                    if v___x_4551_ == 0 {
                        leanh::lean_del_object(v___x_4546_);
                        leanh::lean_inc(v_indName_4537_);
                        v___x_4552_ = l_Lean_mkCasesOnName(v_indName_4537_);
                        v___x_4553_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1(v___x_4552_, v_a_4538_, v_a_4539_, v_a_4540_, v_a_4541_);
                        if leanh::lean_obj_tag(v___x_4553_) == 0 {
                            v_a_4554_ = leanh::lean_ctor_get(v___x_4553_, 0);
                            leanh::lean_inc(v_a_4554_);
                            leanh::lean_dec_ref_known(v___x_4553_, 1);
                            v_levelParams_4555_ = leanh::lean_ctor_get(v_a_4554_, 1);
                            leanh::lean_inc(v_levelParams_4555_);
                            v_type_4556_ = leanh::lean_ctor_get(v_a_4554_, 2);
                            leanh::lean_inc_ref(v_type_4556_);
                            leanh::lean_dec(v_a_4554_);
                            v___x_4557_ = leanh::lean_box((v___x_4551_) as usize);
                            v___f_4558_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___boxed as *mut core::ffi::c_void, 10, 3);
                            leanh::lean_closure_set(v___f_4558_, 0, v_val_4548_);
                            leanh::lean_closure_set(v___f_4558_, 1, v___x_4550_);
                            leanh::lean_closure_set(v___f_4558_, 2, v___x_4557_);
                            v___x_4559_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_4556_, v___f_4558_, v___x_4551_, v_a_4538_, v_a_4539_, v_a_4540_, v_a_4541_);
                            if leanh::lean_obj_tag(v___x_4559_) == 0 {
                                v_a_4560_ = leanh::lean_ctor_get(v___x_4559_, 0);
                                leanh::lean_inc_n(v_a_4560_, 2);
                                leanh::lean_dec_ref_known(v___x_4559_, 1);
                                leanh::lean_inc(v_a_4541_);
                                leanh::lean_inc_ref(v_a_4540_);
                                leanh::lean_inc(v_a_4539_);
                                leanh::lean_inc_ref(v_a_4538_);
                                v___x_4561_ = lean_infer_type(
                                    v_a_4560_, v_a_4538_, v_a_4539_, v_a_4540_, v_a_4541_,
                                );
                                if leanh::lean_obj_tag(v___x_4561_) == 0 {
                                    v_a_4562_ = leanh::lean_ctor_get(v___x_4561_, 0);
                                    leanh::lean_inc(v_a_4562_);
                                    leanh::lean_dec_ref_known(v___x_4561_, 1);
                                    v___x_4563_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName(v_indName_4537_);
                                    v___x_4564_ = leanh::lean_box(1);
                                    leanh::lean_inc(v___x_4563_);
                                    v___x_4565_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v___x_4563_, v_levelParams_4555_, v_a_4562_, v_a_4560_, v___x_4564_, v_a_4541_);
                                    v_a_4566_ = leanh::lean_ctor_get(v___x_4565_, 0);
                                    v_isSharedCheck_4644_ =
                                        (!leanh::lean_is_exclusive(v___x_4565_)) as u8;
                                    if v_isSharedCheck_4644_ == 0 {
                                        v___x_4568_ = v___x_4565_;
                                        v_isShared_4569_ = v_isSharedCheck_4644_;
                                        state = 2;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4566_);
                                        leanh::lean_dec(v___x_4565_);
                                        v___x_4568_ = leanh::lean_box(0);
                                        v_isShared_4569_ = v_isSharedCheck_4644_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_4560_);
                                    leanh::lean_dec(v_levelParams_4555_);
                                    leanh::lean_dec(v_indName_4537_);
                                    v_a_4645_ = leanh::lean_ctor_get(v___x_4561_, 0);
                                    v_isSharedCheck_4652_ =
                                        (!leanh::lean_is_exclusive(v___x_4561_)) as u8;
                                    if v_isSharedCheck_4652_ == 0 {
                                        v___x_4647_ = v___x_4561_;
                                        v_isShared_4648_ = v_isSharedCheck_4652_;
                                        state = 12;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4645_);
                                        leanh::lean_dec(v___x_4561_);
                                        v___x_4647_ = leanh::lean_box(0);
                                        v_isShared_4648_ = v_isSharedCheck_4652_;
                                        state = 12;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_levelParams_4555_);
                                leanh::lean_dec(v_indName_4537_);
                                v_a_4653_ = leanh::lean_ctor_get(v___x_4559_, 0);
                                v_isSharedCheck_4660_ =
                                    (!leanh::lean_is_exclusive(v___x_4559_)) as u8;
                                if v_isSharedCheck_4660_ == 0 {
                                    v___x_4655_ = v___x_4559_;
                                    v_isShared_4656_ = v_isSharedCheck_4660_;
                                    state = 14;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4653_);
                                    leanh::lean_dec(v___x_4559_);
                                    v___x_4655_ = leanh::lean_box(0);
                                    v_isShared_4656_ = v_isSharedCheck_4660_;
                                    state = 14;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_val_4548_);
                            leanh::lean_dec(v_indName_4537_);
                            v_a_4661_ = leanh::lean_ctor_get(v___x_4553_, 0);
                            v_isSharedCheck_4668_ =
                                (!leanh::lean_is_exclusive(v___x_4553_)) as u8;
                            if v_isSharedCheck_4668_ == 0 {
                                v___x_4663_ = v___x_4553_;
                                v_isShared_4664_ = v_isSharedCheck_4668_;
                                state = 16;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4661_);
                                leanh::lean_dec(v___x_4553_);
                                v___x_4663_ = leanh::lean_box(0);
                                v_isShared_4664_ = v_isSharedCheck_4668_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_val_4548_);
                        leanh::lean_dec(v_indName_4537_);
                        v___x_4669_ = leanh::lean_box(0);
                        if v_isShared_4547_ == 0 {
                            leanh::lean_ctor_set(v___x_4546_, 0, v___x_4669_);
                            v___x_4671_ = v___x_4546_;
                            state = 18;
                            continue;
                        } else {
                            v_reuseFailAlloc_4672_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4672_, 0, v___x_4669_);
                            v___x_4671_ = v_reuseFailAlloc_4672_;
                            state = 18;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_4546_);
                    leanh::lean_dec(v_a_4544_);
                    leanh::lean_dec(v_indName_4537_);
                    v___x_4673_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2_once), _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__2);
                    v___x_4674_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_4673_, v_a_4538_, v_a_4539_, v_a_4540_, v_a_4541_);
                    return v___x_4674_;
                }
            }
            2 => {
                if v_isShared_4569_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4568_, 1);
                    v___x_4571_ = v___x_4568_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4643_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4643_, 0, v_a_4566_);
                    v___x_4571_ = v_reuseFailAlloc_4643_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4572_ = 1;
                v___x_4573_ = l_Lean_addAndCompile(
                    v___x_4571_,
                    v___x_4572_,
                    v___x_4551_,
                    v_a_4540_,
                    v_a_4541_,
                );
                if leanh::lean_obj_tag(v___x_4573_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4573_, 1);
                    v___x_4574_ = lean_st_ref_take(v_a_4541_);
                    v_env_4575_ = leanh::lean_ctor_get(v___x_4574_, 0);
                    v_nextMacroScope_4576_ = leanh::lean_ctor_get(v___x_4574_, 1);
                    v_ngen_4577_ = leanh::lean_ctor_get(v___x_4574_, 2);
                    v_auxDeclNGen_4578_ = leanh::lean_ctor_get(v___x_4574_, 3);
                    v_traceState_4579_ = leanh::lean_ctor_get(v___x_4574_, 4);
                    v_messages_4580_ = leanh::lean_ctor_get(v___x_4574_, 6);
                    v_infoState_4581_ = leanh::lean_ctor_get(v___x_4574_, 7);
                    v_snapshotTasks_4582_ = leanh::lean_ctor_get(v___x_4574_, 8);
                    v_isSharedCheck_4641_ = (!leanh::lean_is_exclusive(v___x_4574_)) as u8;
                    if v_isSharedCheck_4641_ == 0 {
                        v_unused_4642_ = leanh::lean_ctor_get(v___x_4574_, 5);
                        leanh::lean_dec(v_unused_4642_);
                        v___x_4584_ = v___x_4574_;
                        v_isShared_4585_ = v_isSharedCheck_4641_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_4582_);
                        leanh::lean_inc(v_infoState_4581_);
                        leanh::lean_inc(v_messages_4580_);
                        leanh::lean_inc(v_traceState_4579_);
                        leanh::lean_inc(v_auxDeclNGen_4578_);
                        leanh::lean_inc(v_ngen_4577_);
                        leanh::lean_inc(v_nextMacroScope_4576_);
                        leanh::lean_inc(v_env_4575_);
                        leanh::lean_dec(v___x_4574_);
                        v___x_4584_ = leanh::lean_box(0);
                        v_isShared_4585_ = v_isSharedCheck_4641_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_4563_);
                    return v___x_4573_;
                }
            }
            4 => {
                leanh::lean_inc(v___x_4563_);
                v___x_4586_ = l_Lean_Meta_addToCompletionBlackList(v_env_4575_, v___x_4563_);
                v___x_4587_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2);
                if v_isShared_4585_ == 0 {
                    leanh::lean_ctor_set(v___x_4584_, 5, v___x_4587_);
                    leanh::lean_ctor_set(v___x_4584_, 0, v___x_4586_);
                    v___x_4589_ = v___x_4584_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4640_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4640_, 0, v___x_4586_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4640_, 1, v_nextMacroScope_4576_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4640_, 2, v_ngen_4577_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4640_, 3, v_auxDeclNGen_4578_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4640_, 4, v_traceState_4579_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4640_, 5, v___x_4587_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4640_, 6, v_messages_4580_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4640_, 7, v_infoState_4581_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4640_, 8, v_snapshotTasks_4582_);
                    v___x_4589_ = v_reuseFailAlloc_4640_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4590_ = lean_st_ref_set(v_a_4541_, v___x_4589_);
                v___x_4591_ = lean_st_ref_take(v_a_4539_);
                v_mctx_4592_ = leanh::lean_ctor_get(v___x_4591_, 0);
                v_zetaDeltaFVarIds_4593_ = leanh::lean_ctor_get(v___x_4591_, 2);
                v_postponed_4594_ = leanh::lean_ctor_get(v___x_4591_, 3);
                v_diag_4595_ = leanh::lean_ctor_get(v___x_4591_, 4);
                v_isSharedCheck_4638_ = (!leanh::lean_is_exclusive(v___x_4591_)) as u8;
                if v_isSharedCheck_4638_ == 0 {
                    v_unused_4639_ = leanh::lean_ctor_get(v___x_4591_, 1);
                    leanh::lean_dec(v_unused_4639_);
                    v___x_4597_ = v___x_4591_;
                    v_isShared_4598_ = v_isSharedCheck_4638_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_4595_);
                    leanh::lean_inc(v_postponed_4594_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_4593_);
                    leanh::lean_inc(v_mctx_4592_);
                    leanh::lean_dec(v___x_4591_);
                    v___x_4597_ = leanh::lean_box(0);
                    v_isShared_4598_ = v_isSharedCheck_4638_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4599_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3);
                if v_isShared_4598_ == 0 {
                    leanh::lean_ctor_set(v___x_4597_, 1, v___x_4599_);
                    v___x_4601_ = v___x_4597_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4637_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4637_, 0, v_mctx_4592_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4637_, 1, v___x_4599_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4637_,
                        2,
                        v_zetaDeltaFVarIds_4593_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4637_, 3, v_postponed_4594_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4637_, 4, v_diag_4595_);
                    v___x_4601_ = v_reuseFailAlloc_4637_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4602_ = lean_st_ref_set(v_a_4539_, v___x_4601_);
                v___x_4603_ = lean_st_ref_take(v_a_4541_);
                v_env_4604_ = leanh::lean_ctor_get(v___x_4603_, 0);
                v_nextMacroScope_4605_ = leanh::lean_ctor_get(v___x_4603_, 1);
                v_ngen_4606_ = leanh::lean_ctor_get(v___x_4603_, 2);
                v_auxDeclNGen_4607_ = leanh::lean_ctor_get(v___x_4603_, 3);
                v_traceState_4608_ = leanh::lean_ctor_get(v___x_4603_, 4);
                v_messages_4609_ = leanh::lean_ctor_get(v___x_4603_, 6);
                v_infoState_4610_ = leanh::lean_ctor_get(v___x_4603_, 7);
                v_snapshotTasks_4611_ = leanh::lean_ctor_get(v___x_4603_, 8);
                v_isSharedCheck_4635_ = (!leanh::lean_is_exclusive(v___x_4603_)) as u8;
                if v_isSharedCheck_4635_ == 0 {
                    v_unused_4636_ = leanh::lean_ctor_get(v___x_4603_, 5);
                    leanh::lean_dec(v_unused_4636_);
                    v___x_4613_ = v___x_4603_;
                    v_isShared_4614_ = v_isSharedCheck_4635_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4611_);
                    leanh::lean_inc(v_infoState_4610_);
                    leanh::lean_inc(v_messages_4609_);
                    leanh::lean_inc(v_traceState_4608_);
                    leanh::lean_inc(v_auxDeclNGen_4607_);
                    leanh::lean_inc(v_ngen_4606_);
                    leanh::lean_inc(v_nextMacroScope_4605_);
                    leanh::lean_inc(v_env_4604_);
                    leanh::lean_dec(v___x_4603_);
                    v___x_4613_ = leanh::lean_box(0);
                    v_isShared_4614_ = v_isSharedCheck_4635_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                leanh::lean_inc(v___x_4563_);
                v___x_4615_ = l_Lean_addProtected(v_env_4604_, v___x_4563_);
                if v_isShared_4614_ == 0 {
                    leanh::lean_ctor_set(v___x_4613_, 5, v___x_4587_);
                    leanh::lean_ctor_set(v___x_4613_, 0, v___x_4615_);
                    v___x_4617_ = v___x_4613_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4634_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4634_, 0, v___x_4615_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4634_, 1, v_nextMacroScope_4605_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4634_, 2, v_ngen_4606_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4634_, 3, v_auxDeclNGen_4607_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4634_, 4, v_traceState_4608_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4634_, 5, v___x_4587_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4634_, 6, v_messages_4609_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4634_, 7, v_infoState_4610_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4634_, 8, v_snapshotTasks_4611_);
                    v___x_4617_ = v_reuseFailAlloc_4634_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_4618_ = lean_st_ref_set(v_a_4541_, v___x_4617_);
                v___x_4619_ = lean_st_ref_take(v_a_4539_);
                v_mctx_4620_ = leanh::lean_ctor_get(v___x_4619_, 0);
                v_zetaDeltaFVarIds_4621_ = leanh::lean_ctor_get(v___x_4619_, 2);
                v_postponed_4622_ = leanh::lean_ctor_get(v___x_4619_, 3);
                v_diag_4623_ = leanh::lean_ctor_get(v___x_4619_, 4);
                v_isSharedCheck_4632_ = (!leanh::lean_is_exclusive(v___x_4619_)) as u8;
                if v_isSharedCheck_4632_ == 0 {
                    v_unused_4633_ = leanh::lean_ctor_get(v___x_4619_, 1);
                    leanh::lean_dec(v_unused_4633_);
                    v___x_4625_ = v___x_4619_;
                    v_isShared_4626_ = v_isSharedCheck_4632_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_4623_);
                    leanh::lean_inc(v_postponed_4622_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_4621_);
                    leanh::lean_inc(v_mctx_4620_);
                    leanh::lean_dec(v___x_4619_);
                    v___x_4625_ = leanh::lean_box(0);
                    v_isShared_4626_ = v_isSharedCheck_4632_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_4626_ == 0 {
                    leanh::lean_ctor_set(v___x_4625_, 1, v___x_4599_);
                    v___x_4628_ = v___x_4625_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4631_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4631_, 0, v_mctx_4620_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4631_, 1, v___x_4599_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4631_,
                        2,
                        v_zetaDeltaFVarIds_4621_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4631_, 3, v_postponed_4622_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4631_, 4, v_diag_4623_);
                    v___x_4628_ = v_reuseFailAlloc_4631_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_4629_ = lean_st_ref_set(v_a_4539_, v___x_4628_);
                v___x_4630_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(v___x_4563_, v_a_4538_, v_a_4539_, v_a_4540_, v_a_4541_);
                return v___x_4630_;
            }
            12 => {
                if v_isShared_4648_ == 0 {
                    v___x_4650_ = v___x_4647_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4651_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4651_, 0, v_a_4645_);
                    v___x_4650_ = v_reuseFailAlloc_4651_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4650_;
            }
            14 => {
                if v_isShared_4656_ == 0 {
                    v___x_4658_ = v___x_4655_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4659_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4659_, 0, v_a_4653_);
                    v___x_4658_ = v_reuseFailAlloc_4659_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4658_;
            }
            16 => {
                if v_isShared_4664_ == 0 {
                    v___x_4666_ = v___x_4663_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4667_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4667_, 0, v_a_4661_);
                    v___x_4666_ = v_reuseFailAlloc_4667_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4666_;
            }
            18 => {
                return v___x_4671_;
            }
            19 => {
                if v_isShared_4679_ == 0 {
                    v___x_4681_ = v___x_4678_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4682_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4682_, 0, v_a_4676_);
                    v___x_4681_ = v_reuseFailAlloc_4682_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4681_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___boxed(
    mut v_indName_4684_: *mut leanh::LeanObject,
    mut v_a_4685_: *mut leanh::LeanObject,
    mut v_a_4686_: *mut leanh::LeanObject,
    mut v_a_4687_: *mut leanh::LeanObject,
    mut v_a_4688_: *mut leanh::LeanObject,
    mut v_a_4689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4690_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType(
        v_indName_4684_,
        v_a_4685_,
        v_a_4686_,
        v_a_4687_,
        v_a_4688_,
    );
    leanh::lean_dec(v_a_4688_);
    leanh::lean_dec_ref(v_a_4687_);
    leanh::lean_dec(v_a_4686_);
    leanh::lean_dec_ref(v_a_4685_);
    return v_res_4690_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_spec__4(
    mut v_00_u03b1_4691_: *mut leanh::LeanObject,
    mut v_name_4692_: *mut leanh::LeanObject,
    mut v_bi_4693_: u8,
    mut v_type_4694_: *mut leanh::LeanObject,
    mut v_k_4695_: *mut leanh::LeanObject,
    mut v_kind_4696_: u8,
    mut v___y_4697_: *mut leanh::LeanObject,
    mut v___y_4698_: *mut leanh::LeanObject,
    mut v___y_4699_: *mut leanh::LeanObject,
    mut v___y_4700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4702_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_spec__4___redArg(v_name_4692_, v_bi_4693_, v_type_4694_, v_k_4695_, v_kind_4696_, v___y_4697_, v___y_4698_, v___y_4699_, v___y_4700_);
    return v___x_4702_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_spec__4___boxed(
    mut v_00_u03b1_4703_: *mut leanh::LeanObject,
    mut v_name_4704_: *mut leanh::LeanObject,
    mut v_bi_4705_: *mut leanh::LeanObject,
    mut v_type_4706_: *mut leanh::LeanObject,
    mut v_k_4707_: *mut leanh::LeanObject,
    mut v_kind_4708_: *mut leanh::LeanObject,
    mut v___y_4709_: *mut leanh::LeanObject,
    mut v___y_4710_: *mut leanh::LeanObject,
    mut v___y_4711_: *mut leanh::LeanObject,
    mut v___y_4712_: *mut leanh::LeanObject,
    mut v___y_4713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_4714_: u8 = 0;
    let mut v_kind_boxed_4715_: u8 = 0;
    let mut v_res_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_4714_ = (leanh::lean_unbox(v_bi_4705_) as u8);
    v_kind_boxed_4715_ = (leanh::lean_unbox(v_kind_4708_) as u8);
    v_res_4716_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3_spec__4(v_00_u03b1_4703_, v_name_4704_, v_bi_boxed_4714_, v_type_4706_, v_k_4707_, v_kind_boxed_4715_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_);
    leanh::lean_dec(v___y_4712_);
    leanh::lean_dec_ref(v___y_4711_);
    leanh::lean_dec(v___y_4710_);
    leanh::lean_dec_ref(v___y_4709_);
    return v_res_4716_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(
    mut v_00_u03b1_4717_: *mut leanh::LeanObject,
    mut v_name_4718_: *mut leanh::LeanObject,
    mut v_type_4719_: *mut leanh::LeanObject,
    mut v_k_4720_: *mut leanh::LeanObject,
    mut v___y_4721_: *mut leanh::LeanObject,
    mut v___y_4722_: *mut leanh::LeanObject,
    mut v___y_4723_: *mut leanh::LeanObject,
    mut v___y_4724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4726_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___redArg(v_name_4718_, v_type_4719_, v_k_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_);
    return v___x_4726_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___boxed(
    mut v_00_u03b1_4727_: *mut leanh::LeanObject,
    mut v_name_4728_: *mut leanh::LeanObject,
    mut v_type_4729_: *mut leanh::LeanObject,
    mut v_k_4730_: *mut leanh::LeanObject,
    mut v___y_4731_: *mut leanh::LeanObject,
    mut v___y_4732_: *mut leanh::LeanObject,
    mut v___y_4733_: *mut leanh::LeanObject,
    mut v___y_4734_: *mut leanh::LeanObject,
    mut v___y_4735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4736_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3(v_00_u03b1_4727_, v_name_4728_, v_type_4729_, v_k_4730_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_);
    leanh::lean_dec(v___y_4734_);
    leanh::lean_dec_ref(v___y_4733_);
    leanh::lean_dec(v___y_4732_);
    leanh::lean_dec_ref(v___y_4731_);
    return v_res_4736_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8(
    mut v_declName_4737_: *mut leanh::LeanObject,
    mut v_s_4738_: u8,
    mut v___y_4739_: *mut leanh::LeanObject,
    mut v___y_4740_: *mut leanh::LeanObject,
    mut v___y_4741_: *mut leanh::LeanObject,
    mut v___y_4742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4744_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg(v_declName_4737_, v_s_4738_, v___y_4740_, v___y_4742_);
    return v___x_4744_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___boxed(
    mut v_declName_4745_: *mut leanh::LeanObject,
    mut v_s_4746_: *mut leanh::LeanObject,
    mut v___y_4747_: *mut leanh::LeanObject,
    mut v___y_4748_: *mut leanh::LeanObject,
    mut v___y_4749_: *mut leanh::LeanObject,
    mut v___y_4750_: *mut leanh::LeanObject,
    mut v___y_4751_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_boxed_4752_: u8 = 0;
    let mut v_res_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_s_boxed_4752_ = (leanh::lean_unbox(v_s_4746_) as u8);
    v_res_4753_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8(v_declName_4745_, v_s_boxed_4752_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_);
    leanh::lean_dec(v___y_4750_);
    leanh::lean_dec_ref(v___y_4749_);
    leanh::lean_dec(v___y_4748_);
    leanh::lean_dec_ref(v___y_4747_);
    return v_res_4753_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0(
    mut v_00_u03b1_4754_: *mut leanh::LeanObject,
    mut v_constName_4755_: *mut leanh::LeanObject,
    mut v___y_4756_: *mut leanh::LeanObject,
    mut v___y_4757_: *mut leanh::LeanObject,
    mut v___y_4758_: *mut leanh::LeanObject,
    mut v___y_4759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4761_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___redArg(v_constName_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_);
    return v___x_4761_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0___boxed(
    mut v_00_u03b1_4762_: *mut leanh::LeanObject,
    mut v_constName_4763_: *mut leanh::LeanObject,
    mut v___y_4764_: *mut leanh::LeanObject,
    mut v___y_4765_: *mut leanh::LeanObject,
    mut v___y_4766_: *mut leanh::LeanObject,
    mut v___y_4767_: *mut leanh::LeanObject,
    mut v___y_4768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4769_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4769_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0(v_00_u03b1_4762_, v_constName_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
    leanh::lean_dec(v___y_4767_);
    leanh::lean_dec_ref(v___y_4766_);
    leanh::lean_dec(v___y_4765_);
    leanh::lean_dec_ref(v___y_4764_);
    return v_res_4769_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4(
    mut v_00_u03b1_4770_: *mut leanh::LeanObject,
    mut v_ref_4771_: *mut leanh::LeanObject,
    mut v_constName_4772_: *mut leanh::LeanObject,
    mut v___y_4773_: *mut leanh::LeanObject,
    mut v___y_4774_: *mut leanh::LeanObject,
    mut v___y_4775_: *mut leanh::LeanObject,
    mut v___y_4776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4778_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg(v_ref_4771_, v_constName_4772_, v___y_4773_, v___y_4774_, v___y_4775_, v___y_4776_);
    return v___x_4778_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___boxed(
    mut v_00_u03b1_4779_: *mut leanh::LeanObject,
    mut v_ref_4780_: *mut leanh::LeanObject,
    mut v_constName_4781_: *mut leanh::LeanObject,
    mut v___y_4782_: *mut leanh::LeanObject,
    mut v___y_4783_: *mut leanh::LeanObject,
    mut v___y_4784_: *mut leanh::LeanObject,
    mut v___y_4785_: *mut leanh::LeanObject,
    mut v___y_4786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4787_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4(v_00_u03b1_4779_, v_ref_4780_, v_constName_4781_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_);
    leanh::lean_dec(v___y_4785_);
    leanh::lean_dec_ref(v___y_4784_);
    leanh::lean_dec(v___y_4783_);
    leanh::lean_dec_ref(v___y_4782_);
    leanh::lean_dec(v_ref_4780_);
    return v_res_4787_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11(
    mut v_00_u03b1_4788_: *mut leanh::LeanObject,
    mut v_ref_4789_: *mut leanh::LeanObject,
    mut v_msg_4790_: *mut leanh::LeanObject,
    mut v_declHint_4791_: *mut leanh::LeanObject,
    mut v___y_4792_: *mut leanh::LeanObject,
    mut v___y_4793_: *mut leanh::LeanObject,
    mut v___y_4794_: *mut leanh::LeanObject,
    mut v___y_4795_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4797_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___redArg(v_ref_4789_, v_msg_4790_, v_declHint_4791_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_);
    return v___x_4797_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11___boxed(
    mut v_00_u03b1_4798_: *mut leanh::LeanObject,
    mut v_ref_4799_: *mut leanh::LeanObject,
    mut v_msg_4800_: *mut leanh::LeanObject,
    mut v_declHint_4801_: *mut leanh::LeanObject,
    mut v___y_4802_: *mut leanh::LeanObject,
    mut v___y_4803_: *mut leanh::LeanObject,
    mut v___y_4804_: *mut leanh::LeanObject,
    mut v___y_4805_: *mut leanh::LeanObject,
    mut v___y_4806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4807_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11(v_00_u03b1_4798_, v_ref_4799_, v_msg_4800_, v_declHint_4801_, v___y_4802_, v___y_4803_, v___y_4804_, v___y_4805_);
    leanh::lean_dec(v___y_4805_);
    leanh::lean_dec_ref(v___y_4804_);
    leanh::lean_dec(v___y_4803_);
    leanh::lean_dec_ref(v___y_4802_);
    leanh::lean_dec(v_ref_4799_);
    return v_res_4807_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(
    mut v_msg_4808_: *mut leanh::LeanObject,
    mut v_declHint_4809_: *mut leanh::LeanObject,
    mut v___y_4810_: *mut leanh::LeanObject,
    mut v___y_4811_: *mut leanh::LeanObject,
    mut v___y_4812_: *mut leanh::LeanObject,
    mut v___y_4813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4815_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg(v_msg_4808_, v_declHint_4809_, v___y_4813_);
    return v___x_4815_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___boxed(
    mut v_msg_4816_: *mut leanh::LeanObject,
    mut v_declHint_4817_: *mut leanh::LeanObject,
    mut v___y_4818_: *mut leanh::LeanObject,
    mut v___y_4819_: *mut leanh::LeanObject,
    mut v___y_4820_: *mut leanh::LeanObject,
    mut v___y_4821_: *mut leanh::LeanObject,
    mut v___y_4822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4823_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13(v_msg_4816_, v_declHint_4817_, v___y_4818_, v___y_4819_, v___y_4820_, v___y_4821_);
    leanh::lean_dec(v___y_4821_);
    leanh::lean_dec_ref(v___y_4820_);
    leanh::lean_dec(v___y_4819_);
    leanh::lean_dec_ref(v___y_4818_);
    return v_res_4823_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13(
    mut v_00_u03b1_4824_: *mut leanh::LeanObject,
    mut v_ref_4825_: *mut leanh::LeanObject,
    mut v_msg_4826_: *mut leanh::LeanObject,
    mut v___y_4827_: *mut leanh::LeanObject,
    mut v___y_4828_: *mut leanh::LeanObject,
    mut v___y_4829_: *mut leanh::LeanObject,
    mut v___y_4830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4832_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___redArg(v_ref_4825_, v_msg_4826_, v___y_4827_, v___y_4828_, v___y_4829_, v___y_4830_);
    return v___x_4832_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13___boxed(
    mut v_00_u03b1_4833_: *mut leanh::LeanObject,
    mut v_ref_4834_: *mut leanh::LeanObject,
    mut v_msg_4835_: *mut leanh::LeanObject,
    mut v___y_4836_: *mut leanh::LeanObject,
    mut v___y_4837_: *mut leanh::LeanObject,
    mut v___y_4838_: *mut leanh::LeanObject,
    mut v___y_4839_: *mut leanh::LeanObject,
    mut v___y_4840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4841_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__13(v_00_u03b1_4833_, v_ref_4834_, v_msg_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
    leanh::lean_dec(v___y_4839_);
    leanh::lean_dec_ref(v___y_4838_);
    leanh::lean_dec(v___y_4837_);
    leanh::lean_dec_ref(v___y_4836_);
    leanh::lean_dec(v_ref_4834_);
    return v_res_4841_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__0(
    mut v___x_4842_: *mut leanh::LeanObject,
    mut v_k_4843_: *mut leanh::LeanObject,
    mut v_zs_4844_: *mut leanh::LeanObject,
    mut v_isZero_4845_: u8,
    mut v___x_4846_: u8,
    mut v___x_4847_: u8,
    mut v_h_4848_: *mut leanh::LeanObject,
    mut v___y_4849_: *mut leanh::LeanObject,
    mut v___y_4850_: *mut leanh::LeanObject,
    mut v___y_4851_: *mut leanh::LeanObject,
    mut v___y_4852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4854_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_h_4848_);
    v___x_4854_ = l_Lean_Meta_mkEqNDRec(
        v___x_4842_,
        v_k_4843_,
        v_h_4848_,
        v___y_4849_,
        v___y_4850_,
        v___y_4851_,
        v___y_4852_,
    );
    if leanh::lean_obj_tag(v___x_4854_) == 0 {
        let mut v_a_4855_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4856_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_4855_ = leanh::lean_ctor_get(v___x_4854_, 0);
        leanh::lean_inc(v_a_4855_);
        leanh::lean_dec_ref_known(v___x_4854_, 1);
        v___x_4856_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkPULiftDown(
            v_a_4855_,
            v___y_4849_,
            v___y_4850_,
            v___y_4851_,
            v___y_4852_,
        );
        if leanh::lean_obj_tag(v___x_4856_) == 0 {
            let mut v_a_4857_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4858_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4859_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_4857_ = leanh::lean_ctor_get(v___x_4856_, 0);
            leanh::lean_inc(v_a_4857_);
            leanh::lean_dec_ref_known(v___x_4856_, 1);
            v___x_4858_ = l_Lean_mkAppN(v_a_4857_, v_zs_4844_);
            v___x_4859_ = lean_array_push(v_zs_4844_, v_h_4848_);
            v___x_4860_ = l_Lean_Meta_mkLambdaFVars(
                v___x_4859_,
                v___x_4858_,
                v_isZero_4845_,
                v___x_4846_,
                v_isZero_4845_,
                v___x_4846_,
                v___x_4847_,
                v___y_4849_,
                v___y_4850_,
                v___y_4851_,
                v___y_4852_,
            );
            leanh::lean_dec_ref(v___x_4859_);
            return v___x_4860_;
        } else {
            leanh::lean_dec_ref(v_h_4848_);
            leanh::lean_dec_ref(v_zs_4844_);
            return v___x_4856_;
        }
    } else {
        leanh::lean_dec_ref(v_h_4848_);
        leanh::lean_dec_ref(v_zs_4844_);
        return v___x_4854_;
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__0___boxed(
    mut v___x_4861_: *mut leanh::LeanObject,
    mut v_k_4862_: *mut leanh::LeanObject,
    mut v_zs_4863_: *mut leanh::LeanObject,
    mut v_isZero_4864_: *mut leanh::LeanObject,
    mut v___x_4865_: *mut leanh::LeanObject,
    mut v___x_4866_: *mut leanh::LeanObject,
    mut v_h_4867_: *mut leanh::LeanObject,
    mut v___y_4868_: *mut leanh::LeanObject,
    mut v___y_4869_: *mut leanh::LeanObject,
    mut v___y_4870_: *mut leanh::LeanObject,
    mut v___y_4871_: *mut leanh::LeanObject,
    mut v___y_4872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isZero_boxed_4873_: u8 = 0;
    let mut v___x_6039__boxed_4874_: u8 = 0;
    let mut v___x_6040__boxed_4875_: u8 = 0;
    let mut v_res_4876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isZero_boxed_4873_ = (leanh::lean_unbox(v_isZero_4864_) as u8);
    v___x_6039__boxed_4874_ = (leanh::lean_unbox(v___x_4865_) as u8);
    v___x_6040__boxed_4875_ = (leanh::lean_unbox(v___x_4866_) as u8);
    v_res_4876_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__0(v___x_4861_, v_k_4862_, v_zs_4863_, v_isZero_boxed_4873_, v___x_6039__boxed_4874_, v___x_6040__boxed_4875_, v_h_4867_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_);
    leanh::lean_dec(v___y_4871_);
    leanh::lean_dec_ref(v___y_4870_);
    leanh::lean_dec(v___y_4869_);
    leanh::lean_dec_ref(v___y_4868_);
    return v_res_4876_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1(
    mut v___x_4880_: *mut leanh::LeanObject,
    mut v_k_4881_: *mut leanh::LeanObject,
    mut v_isZero_4882_: u8,
    mut v___x_4883_: u8,
    mut v___x_4884_: u8,
    mut v___x_4885_: *mut leanh::LeanObject,
    mut v___x_4886_: *mut leanh::LeanObject,
    mut v_j_4887_: *mut leanh::LeanObject,
    mut v___x_4888_: *mut leanh::LeanObject,
    mut v_ctorIdx_4889_: *mut leanh::LeanObject,
    mut v___x_4890_: *mut leanh::LeanObject,
    mut v_zs_4891_: *mut leanh::LeanObject,
    mut v___ctorRet_4892_: *mut leanh::LeanObject,
    mut v___y_4893_: *mut leanh::LeanObject,
    mut v___y_4894_: *mut leanh::LeanObject,
    mut v___y_4895_: *mut leanh::LeanObject,
    mut v___y_4896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4898_ = leanh::lean_box((v_isZero_4882_) as usize);
    v___x_4899_ = leanh::lean_box((v___x_4883_) as usize);
    v___x_4900_ = leanh::lean_box((v___x_4884_) as usize);
    v___f_4901_ = leanh::lean_alloc_closure(l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 12, 6);
    leanh::lean_closure_set(v___f_4901_, 0, v___x_4880_);
    leanh::lean_closure_set(v___f_4901_, 1, v_k_4881_);
    leanh::lean_closure_set(v___f_4901_, 2, v_zs_4891_);
    leanh::lean_closure_set(v___f_4901_, 3, v___x_4898_);
    leanh::lean_closure_set(v___f_4901_, 4, v___x_4899_);
    leanh::lean_closure_set(v___f_4901_, 5, v___x_4900_);
    v___x_4902_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___closed__1;
    v___x_4903_ = l_Lean_Level_ofNat(v___x_4885_);
    v___x_4904_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4904_, 0, v___x_4903_);
    leanh::lean_ctor_set(v___x_4904_, 1, v___x_4886_);
    v___x_4905_ = l_Lean_mkConst(v___x_4902_, v___x_4904_);
    v___x_4906_ = l_Lean_mkRawNatLit(v_j_4887_);
    v___x_4907_ = l_Lean_mkApp3(v___x_4905_, v___x_4888_, v_ctorIdx_4889_, v___x_4906_);
    v___x_4908_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___redArg(v___x_4890_, v___x_4907_, v___f_4901_, v___y_4893_, v___y_4894_, v___y_4895_, v___y_4896_);
    return v___x_4908_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4909_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_k_4910_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_isZero_4911_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___x_4912_: *mut leanh::LeanObject = *_args.add(3);
    let mut v___x_4913_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___x_4914_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___x_4915_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_j_4916_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___x_4917_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_ctorIdx_4918_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___x_4919_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_zs_4920_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___ctorRet_4921_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_4922_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_4923_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_4924_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_4925_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_4926_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_isZero_boxed_4927_: u8 = 0;
    let mut v___x_6085__boxed_4928_: u8 = 0;
    let mut v___x_6086__boxed_4929_: u8 = 0;
    let mut v_res_4930_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isZero_boxed_4927_ = (leanh::lean_unbox(v_isZero_4911_) as u8);
    v___x_6085__boxed_4928_ = (leanh::lean_unbox(v___x_4912_) as u8);
    v___x_6086__boxed_4929_ = (leanh::lean_unbox(v___x_4913_) as u8);
    v_res_4930_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1(v___x_4909_, v_k_4910_, v_isZero_boxed_4927_, v___x_6085__boxed_4928_, v___x_6086__boxed_4929_, v___x_4914_, v___x_4915_, v_j_4916_, v___x_4917_, v_ctorIdx_4918_, v___x_4919_, v_zs_4920_, v___ctorRet_4921_, v___y_4922_, v___y_4923_, v___y_4924_, v___y_4925_);
    leanh::lean_dec(v___y_4925_);
    leanh::lean_dec_ref(v___y_4924_);
    leanh::lean_dec(v___y_4923_);
    leanh::lean_dec_ref(v___y_4922_);
    leanh::lean_dec_ref(v___ctorRet_4921_);
    leanh::lean_dec(v___x_4914_);
    return v_res_4930_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg(
    mut v___x_4934_: *mut leanh::LeanObject,
    mut v_k_4935_: *mut leanh::LeanObject,
    mut v_ctorIdx_4936_: *mut leanh::LeanObject,
    mut v_tail_4937_: *mut leanh::LeanObject,
    mut v___x_4938_: *mut leanh::LeanObject,
    mut v_as_4939_: *mut leanh::LeanObject,
    mut v_i_4940_: *mut leanh::LeanObject,
    mut v_j_4941_: *mut leanh::LeanObject,
    mut v_bs_4942_: *mut leanh::LeanObject,
    mut v___y_4943_: *mut leanh::LeanObject,
    mut v___y_4944_: *mut leanh::LeanObject,
    mut v___y_4945_: *mut leanh::LeanObject,
    mut v___y_4946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4949_: u8 = 0;
    let mut v___x_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4962_: u8 = 0;
    let mut v___x_4964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4966_: u8 = 0;
    let mut v___x_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: u8 = 0;
    let mut v___x_4973_: u8 = 0;
    let mut v___x_4974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_4948_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_4949_ = lean_nat_dec_eq(v_i_4940_, v_zero_4948_);
                if v_isZero_4949_ == 1 {
                    leanh::lean_dec(v_j_4941_);
                    leanh::lean_dec(v_i_4940_);
                    leanh::lean_dec(v_tail_4937_);
                    leanh::lean_dec_ref(v_ctorIdx_4936_);
                    leanh::lean_dec_ref(v_k_4935_);
                    leanh::lean_dec_ref(v___x_4934_);
                    v___x_4950_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4950_, 0, v_bs_4942_);
                    return v___x_4950_;
                } else {
                    v___x_4951_ = leanh::lean_unsigned_to_nat(1);
                    v_n_4952_ = lean_nat_sub(v_i_4940_, v___x_4951_);
                    leanh::lean_dec(v_i_4940_);
                    v___x_4967_ = lean_array_fget_borrowed(v_as_4939_, v_j_4941_);
                    leanh::lean_inc(v_tail_4937_);
                    leanh::lean_inc(v___x_4967_);
                    v___x_4968_ = l_Lean_mkConst(v___x_4967_, v_tail_4937_);
                    v___x_4969_ = l_Lean_mkAppN(v___x_4968_, v___x_4938_);
                    leanh::lean_inc(v___y_4946_);
                    leanh::lean_inc_ref(v___y_4945_);
                    leanh::lean_inc(v___y_4944_);
                    leanh::lean_inc_ref(v___y_4943_);
                    v___x_4970_ = lean_infer_type(
                        v___x_4969_,
                        v___y_4943_,
                        v___y_4944_,
                        v___y_4945_,
                        v___y_4946_,
                    );
                    if leanh::lean_obj_tag(v___x_4970_) == 0 {
                        v_a_4971_ = leanh::lean_ctor_get(v___x_4970_, 0);
                        leanh::lean_inc(v_a_4971_);
                        leanh::lean_dec_ref_known(v___x_4970_, 1);
                        v___x_4972_ = 1;
                        v___x_4973_ = 1;
                        v___x_4974_ = leanh::lean_box(0);
                        v___x_4975_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4_once), _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__4);
                        v___x_4976_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__1;
                        v___x_4977_ = leanh::lean_box((v_isZero_4949_) as usize);
                        v___x_4978_ = leanh::lean_box((v___x_4972_) as usize);
                        v___x_4979_ = leanh::lean_box((v___x_4973_) as usize);
                        leanh::lean_inc_ref(v_ctorIdx_4936_);
                        leanh::lean_inc(v_j_4941_);
                        leanh::lean_inc_ref(v_k_4935_);
                        leanh::lean_inc_ref(v___x_4934_);
                        v___f_4980_ = leanh::lean_alloc_closure(l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___lam__1___boxed as *mut core::ffi::c_void, 18, 11);
                        leanh::lean_closure_set(v___f_4980_, 0, v___x_4934_);
                        leanh::lean_closure_set(v___f_4980_, 1, v_k_4935_);
                        leanh::lean_closure_set(v___f_4980_, 2, v___x_4977_);
                        leanh::lean_closure_set(v___f_4980_, 3, v___x_4978_);
                        leanh::lean_closure_set(v___f_4980_, 4, v___x_4979_);
                        leanh::lean_closure_set(v___f_4980_, 5, v___x_4951_);
                        leanh::lean_closure_set(v___f_4980_, 6, v___x_4974_);
                        leanh::lean_closure_set(v___f_4980_, 7, v_j_4941_);
                        leanh::lean_closure_set(v___f_4980_, 8, v___x_4975_);
                        leanh::lean_closure_set(v___f_4980_, 9, v_ctorIdx_4936_);
                        leanh::lean_closure_set(v___f_4980_, 10, v___x_4976_);
                        v___x_4981_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_a_4971_, v___f_4980_, v_isZero_4949_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_);
                        v___y_4954_ = v___x_4981_;
                        state = 1;
                        continue;
                    } else {
                        v___y_4954_ = v___x_4970_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_4954_) == 0 {
                    v_a_4955_ = leanh::lean_ctor_get(v___y_4954_, 0);
                    leanh::lean_inc(v_a_4955_);
                    leanh::lean_dec_ref_known(v___y_4954_, 1);
                    v___x_4956_ = lean_nat_add(v_j_4941_, v___x_4951_);
                    leanh::lean_dec(v_j_4941_);
                    v___x_4957_ = lean_array_push(v_bs_4942_, v_a_4955_);
                    v_i_4940_ = v_n_4952_;
                    v_j_4941_ = v___x_4956_;
                    v_bs_4942_ = v___x_4957_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_n_4952_);
                    leanh::lean_dec_ref(v_bs_4942_);
                    leanh::lean_dec(v_j_4941_);
                    leanh::lean_dec(v_tail_4937_);
                    leanh::lean_dec_ref(v_ctorIdx_4936_);
                    leanh::lean_dec_ref(v_k_4935_);
                    leanh::lean_dec_ref(v___x_4934_);
                    v_a_4959_ = leanh::lean_ctor_get(v___y_4954_, 0);
                    v_isSharedCheck_4966_ = (!leanh::lean_is_exclusive(v___y_4954_)) as u8;
                    if v_isSharedCheck_4966_ == 0 {
                        v___x_4961_ = v___y_4954_;
                        v_isShared_4962_ = v_isSharedCheck_4966_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4959_);
                        leanh::lean_dec(v___y_4954_);
                        v___x_4961_ = leanh::lean_box(0);
                        v_isShared_4962_ = v_isSharedCheck_4966_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4962_ == 0 {
                    v___x_4964_ = v___x_4961_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4965_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4965_, 0, v_a_4959_);
                    v___x_4964_ = v_reuseFailAlloc_4965_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4964_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___boxed(
    mut v___x_4982_: *mut leanh::LeanObject,
    mut v_k_4983_: *mut leanh::LeanObject,
    mut v_ctorIdx_4984_: *mut leanh::LeanObject,
    mut v_tail_4985_: *mut leanh::LeanObject,
    mut v___x_4986_: *mut leanh::LeanObject,
    mut v_as_4987_: *mut leanh::LeanObject,
    mut v_i_4988_: *mut leanh::LeanObject,
    mut v_j_4989_: *mut leanh::LeanObject,
    mut v_bs_4990_: *mut leanh::LeanObject,
    mut v___y_4991_: *mut leanh::LeanObject,
    mut v___y_4992_: *mut leanh::LeanObject,
    mut v___y_4993_: *mut leanh::LeanObject,
    mut v___y_4994_: *mut leanh::LeanObject,
    mut v___y_4995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4996_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4996_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg(v___x_4982_, v_k_4983_, v_ctorIdx_4984_, v_tail_4985_, v___x_4986_, v_as_4987_, v_i_4988_, v_j_4989_, v_bs_4990_, v___y_4991_, v___y_4992_, v___y_4993_, v___y_4994_);
    leanh::lean_dec(v___y_4994_);
    leanh::lean_dec_ref(v___y_4993_);
    leanh::lean_dec(v___y_4992_);
    leanh::lean_dec_ref(v___y_4991_);
    leanh::lean_dec_ref(v_as_4987_);
    leanh::lean_dec_ref(v___x_4986_);
    return v_res_4996_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0(
    mut v___x_4997_: *mut leanh::LeanObject,
    mut v___x_4998_: *mut leanh::LeanObject,
    mut v_a_4999_: *mut leanh::LeanObject,
    mut v_ctors_5000_: *mut leanh::LeanObject,
    mut v___x_5001_: *mut leanh::LeanObject,
    mut v_ctorIdx_5002_: *mut leanh::LeanObject,
    mut v_tail_5003_: *mut leanh::LeanObject,
    mut v___x_5004_: *mut leanh::LeanObject,
    mut v___x_5005_: *mut leanh::LeanObject,
    mut v_name_5006_: *mut leanh::LeanObject,
    mut v___x_5007_: *mut leanh::LeanObject,
    mut v_h_5008_: *mut leanh::LeanObject,
    mut v_k_5009_: *mut leanh::LeanObject,
    mut v___y_5010_: *mut leanh::LeanObject,
    mut v___y_5011_: *mut leanh::LeanObject,
    mut v___y_5012_: *mut leanh::LeanObject,
    mut v___y_5013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: u8 = 0;
    let mut v___x_5019_: u8 = 0;
    let mut v___x_5020_: u8 = 0;
    let mut v___x_5021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5047_: u8 = 0;
    let mut v___x_5049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5051_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v___x_4997_);
                v___x_5015_ = l_Lean_mkAppN(v___x_4997_, v___x_4998_);
                v___x_5016_ = l_Lean_mkArrow(v_a_4999_, v___x_5015_, v___y_5012_, v___y_5013_);
                if leanh::lean_obj_tag(v___x_5016_) == 0 {
                    v_a_5017_ = leanh::lean_ctor_get(v___x_5016_, 0);
                    leanh::lean_inc(v_a_5017_);
                    leanh::lean_dec_ref_known(v___x_5016_, 1);
                    v___x_5018_ = 0;
                    v___x_5019_ = 1;
                    v___x_5020_ = 1;
                    v___x_5021_ = l_Lean_Meta_mkLambdaFVars(
                        v___x_4998_,
                        v_a_5017_,
                        v___x_5018_,
                        v___x_5019_,
                        v___x_5018_,
                        v___x_5019_,
                        v___x_5020_,
                        v___y_5010_,
                        v___y_5011_,
                        v___y_5012_,
                        v___y_5013_,
                    );
                    if leanh::lean_obj_tag(v___x_5021_) == 0 {
                        v_a_5022_ = leanh::lean_ctor_get(v___x_5021_, 0);
                        leanh::lean_inc(v_a_5022_);
                        leanh::lean_dec_ref_known(v___x_5021_, 1);
                        v___x_5023_ = lean_array_mk(v_ctors_5000_);
                        v___x_5024_ = lean_array_get_size(v___x_5023_);
                        v___x_5025_ = lean_mk_empty_array_with_capacity(v___x_5024_);
                        leanh::lean_inc_ref(v_ctorIdx_5002_);
                        leanh::lean_inc_ref(v_k_5009_);
                        v___x_5026_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg(v___x_5001_, v_k_5009_, v_ctorIdx_5002_, v_tail_5003_, v___x_5004_, v___x_5023_, v___x_5024_, v___x_5005_, v___x_5025_, v___y_5010_, v___y_5011_, v___y_5012_, v___y_5013_);
                        leanh::lean_dec_ref(v___x_5023_);
                        if leanh::lean_obj_tag(v___x_5026_) == 0 {
                            v_a_5027_ = leanh::lean_ctor_get(v___x_5026_, 0);
                            leanh::lean_inc(v_a_5027_);
                            leanh::lean_dec_ref_known(v___x_5026_, 1);
                            v___x_5028_ = l_Lean_mkConst(v_name_5006_, v___x_5007_);
                            v___x_5029_ = l_Lean_mkAppN(v___x_5028_, v___x_5004_);
                            v___x_5030_ = l_Lean_Expr_app___override(v___x_5029_, v_a_5022_);
                            v___x_5031_ = l_Lean_mkAppN(v___x_5030_, v___x_4998_);
                            v___x_5032_ = l_Lean_mkAppN(v___x_5031_, v_a_5027_);
                            leanh::lean_dec(v_a_5027_);
                            leanh::lean_inc_ref(v_h_5008_);
                            v___x_5033_ = l_Lean_Expr_app___override(v___x_5032_, v_h_5008_);
                            v___x_5034_ = leanh::lean_unsigned_to_nat(2);
                            v___x_5035_ = lean_mk_empty_array_with_capacity(v___x_5034_);
                            leanh::lean_inc_ref(v___x_5035_);
                            v___x_5036_ = lean_array_push(v___x_5035_, v___x_4997_);
                            v___x_5037_ = lean_array_push(v___x_5036_, v_ctorIdx_5002_);
                            v___x_5038_ = l_Array_append___redArg(v___x_5004_, v___x_5037_);
                            leanh::lean_dec_ref(v___x_5037_);
                            v___x_5039_ = l_Array_append___redArg(v___x_5038_, v___x_4998_);
                            v___x_5040_ = lean_array_push(v___x_5035_, v_h_5008_);
                            v___x_5041_ = lean_array_push(v___x_5040_, v_k_5009_);
                            v___x_5042_ = l_Array_append___redArg(v___x_5039_, v___x_5041_);
                            leanh::lean_dec_ref(v___x_5041_);
                            v___x_5043_ = l_Lean_Meta_mkLambdaFVars(
                                v___x_5042_,
                                v___x_5033_,
                                v___x_5018_,
                                v___x_5019_,
                                v___x_5018_,
                                v___x_5019_,
                                v___x_5020_,
                                v___y_5010_,
                                v___y_5011_,
                                v___y_5012_,
                                v___y_5013_,
                            );
                            leanh::lean_dec_ref(v___x_5042_);
                            return v___x_5043_;
                        } else {
                            leanh::lean_dec(v_a_5022_);
                            leanh::lean_dec_ref(v_k_5009_);
                            leanh::lean_dec_ref(v_h_5008_);
                            leanh::lean_dec(v___x_5007_);
                            leanh::lean_dec(v_name_5006_);
                            leanh::lean_dec_ref(v___x_5004_);
                            leanh::lean_dec_ref(v_ctorIdx_5002_);
                            leanh::lean_dec_ref(v___x_4997_);
                            v_a_5044_ = leanh::lean_ctor_get(v___x_5026_, 0);
                            v_isSharedCheck_5051_ =
                                (!leanh::lean_is_exclusive(v___x_5026_)) as u8;
                            if v_isSharedCheck_5051_ == 0 {
                                v___x_5046_ = v___x_5026_;
                                v_isShared_5047_ = v_isSharedCheck_5051_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5044_);
                                leanh::lean_dec(v___x_5026_);
                                v___x_5046_ = leanh::lean_box(0);
                                v_isShared_5047_ = v_isSharedCheck_5051_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_k_5009_);
                        leanh::lean_dec_ref(v_h_5008_);
                        leanh::lean_dec(v___x_5007_);
                        leanh::lean_dec(v_name_5006_);
                        leanh::lean_dec(v___x_5005_);
                        leanh::lean_dec_ref(v___x_5004_);
                        leanh::lean_dec(v_tail_5003_);
                        leanh::lean_dec_ref(v_ctorIdx_5002_);
                        leanh::lean_dec_ref(v___x_5001_);
                        leanh::lean_dec(v_ctors_5000_);
                        leanh::lean_dec_ref(v___x_4997_);
                        return v___x_5021_;
                    }
                } else {
                    leanh::lean_dec_ref(v_k_5009_);
                    leanh::lean_dec_ref(v_h_5008_);
                    leanh::lean_dec(v___x_5007_);
                    leanh::lean_dec(v_name_5006_);
                    leanh::lean_dec(v___x_5005_);
                    leanh::lean_dec_ref(v___x_5004_);
                    leanh::lean_dec(v_tail_5003_);
                    leanh::lean_dec_ref(v_ctorIdx_5002_);
                    leanh::lean_dec_ref(v___x_5001_);
                    leanh::lean_dec(v_ctors_5000_);
                    leanh::lean_dec_ref(v___x_4997_);
                    return v___x_5016_;
                }
            }
            1 => {
                if v_isShared_5047_ == 0 {
                    v___x_5049_ = v___x_5046_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5050_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5050_, 0, v_a_5044_);
                    v___x_5049_ = v_reuseFailAlloc_5050_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5049_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5052_: *mut leanh::LeanObject = *_args.add(0);
    let mut v___x_5053_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_a_5054_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_ctors_5055_: *mut leanh::LeanObject = *_args.add(3);
    let mut v___x_5056_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_ctorIdx_5057_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_tail_5058_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_5059_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___x_5060_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_name_5061_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___x_5062_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_h_5063_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_k_5064_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_5065_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_5066_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_5067_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_5068_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_5069_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_res_5070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5070_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0(
        v___x_5052_,
        v___x_5053_,
        v_a_5054_,
        v_ctors_5055_,
        v___x_5056_,
        v_ctorIdx_5057_,
        v_tail_5058_,
        v___x_5059_,
        v___x_5060_,
        v_name_5061_,
        v___x_5062_,
        v_h_5063_,
        v_k_5064_,
        v___y_5065_,
        v___y_5066_,
        v___y_5067_,
        v___y_5068_,
    );
    leanh::lean_dec(v___y_5068_);
    leanh::lean_dec_ref(v___y_5067_);
    leanh::lean_dec(v___y_5066_);
    leanh::lean_dec_ref(v___y_5065_);
    leanh::lean_dec_ref(v___x_5053_);
    return v_res_5070_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1(
    mut v___x_5074_: *mut leanh::LeanObject,
    mut v___x_5075_: *mut leanh::LeanObject,
    mut v_a_5076_: *mut leanh::LeanObject,
    mut v_ctors_5077_: *mut leanh::LeanObject,
    mut v___x_5078_: *mut leanh::LeanObject,
    mut v_ctorIdx_5079_: *mut leanh::LeanObject,
    mut v_tail_5080_: *mut leanh::LeanObject,
    mut v___x_5081_: *mut leanh::LeanObject,
    mut v___x_5082_: *mut leanh::LeanObject,
    mut v_name_5083_: *mut leanh::LeanObject,
    mut v___x_5084_: *mut leanh::LeanObject,
    mut v___x_5085_: *mut leanh::LeanObject,
    mut v_h_5086_: *mut leanh::LeanObject,
    mut v___y_5087_: *mut leanh::LeanObject,
    mut v___y_5088_: *mut leanh::LeanObject,
    mut v___y_5089_: *mut leanh::LeanObject,
    mut v___y_5090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5092_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__0___boxed
            as *mut core::ffi::c_void,
        18,
        12,
    );
    leanh::lean_closure_set(v___f_5092_, 0, v___x_5074_);
    leanh::lean_closure_set(v___f_5092_, 1, v___x_5075_);
    leanh::lean_closure_set(v___f_5092_, 2, v_a_5076_);
    leanh::lean_closure_set(v___f_5092_, 3, v_ctors_5077_);
    leanh::lean_closure_set(v___f_5092_, 4, v___x_5078_);
    leanh::lean_closure_set(v___f_5092_, 5, v_ctorIdx_5079_);
    leanh::lean_closure_set(v___f_5092_, 6, v_tail_5080_);
    leanh::lean_closure_set(v___f_5092_, 7, v___x_5081_);
    leanh::lean_closure_set(v___f_5092_, 8, v___x_5082_);
    leanh::lean_closure_set(v___f_5092_, 9, v_name_5083_);
    leanh::lean_closure_set(v___f_5092_, 10, v___x_5084_);
    leanh::lean_closure_set(v___f_5092_, 11, v_h_5086_);
    v___x_5093_ =
        l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___closed__1;
    v___x_5094_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___redArg(v___x_5093_, v___x_5085_, v___f_5092_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_);
    return v___x_5094_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5095_: *mut leanh::LeanObject = *_args.add(0);
    let mut v___x_5096_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_a_5097_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_ctors_5098_: *mut leanh::LeanObject = *_args.add(3);
    let mut v___x_5099_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_ctorIdx_5100_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_tail_5101_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_5102_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___x_5103_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_name_5104_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___x_5105_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___x_5106_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_h_5107_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_5108_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_5109_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_5110_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_5111_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_5112_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_res_5113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5113_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1(
        v___x_5095_,
        v___x_5096_,
        v_a_5097_,
        v_ctors_5098_,
        v___x_5099_,
        v_ctorIdx_5100_,
        v_tail_5101_,
        v___x_5102_,
        v___x_5103_,
        v_name_5104_,
        v___x_5105_,
        v___x_5106_,
        v_h_5107_,
        v___y_5108_,
        v___y_5109_,
        v___y_5110_,
        v___y_5111_,
    );
    leanh::lean_dec(v___y_5111_);
    leanh::lean_dec_ref(v___y_5110_);
    leanh::lean_dec(v___y_5109_);
    leanh::lean_dec_ref(v___y_5108_);
    return v_res_5113_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2(
    mut v___x_5114_: *mut leanh::LeanObject,
    mut v___x_5115_: *mut leanh::LeanObject,
    mut v___x_5116_: *mut leanh::LeanObject,
    mut v___x_5117_: *mut leanh::LeanObject,
    mut v_indName_5118_: *mut leanh::LeanObject,
    mut v_tail_5119_: *mut leanh::LeanObject,
    mut v___x_5120_: *mut leanh::LeanObject,
    mut v_ctors_5121_: *mut leanh::LeanObject,
    mut v___x_5122_: *mut leanh::LeanObject,
    mut v_name_5123_: *mut leanh::LeanObject,
    mut v_ctorIdx_5124_: *mut leanh::LeanObject,
    mut v___y_5125_: *mut leanh::LeanObject,
    mut v___y_5126_: *mut leanh::LeanObject,
    mut v___y_5127_: *mut leanh::LeanObject,
    mut v___y_5128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___x_5115_);
    v___x_5130_ = l_Lean_mkConst(v___x_5114_, v___x_5115_);
    leanh::lean_inc_ref(v___x_5117_);
    leanh::lean_inc_ref_n(v___x_5116_, 2);
    v___x_5131_ = lean_array_push(v___x_5116_, v___x_5117_);
    v___x_5132_ = l_Lean_mkAppN(v___x_5130_, v___x_5131_);
    leanh::lean_dec_ref(v___x_5131_);
    leanh::lean_inc_ref_n(v_ctorIdx_5124_, 2);
    leanh::lean_inc_ref(v___x_5132_);
    v___x_5133_ = l_Lean_Expr_app___override(v___x_5132_, v_ctorIdx_5124_);
    v___x_5134_ = l_mkCtorIdxName(v_indName_5118_);
    leanh::lean_inc(v_tail_5119_);
    v___x_5135_ = l_Lean_mkConst(v___x_5134_, v_tail_5119_);
    v___x_5136_ = l_Array_append___redArg(v___x_5116_, v___x_5120_);
    v___x_5137_ = l_Lean_mkAppN(v___x_5135_, v___x_5136_);
    leanh::lean_dec_ref(v___x_5136_);
    v___x_5138_ = l_Lean_Meta_mkEq(
        v_ctorIdx_5124_,
        v___x_5137_,
        v___y_5125_,
        v___y_5126_,
        v___y_5127_,
        v___y_5128_,
    );
    if leanh::lean_obj_tag(v___x_5138_) == 0 {
        let mut v_a_5139_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5140_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5141_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5142_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_5139_ = leanh::lean_ctor_get(v___x_5138_, 0);
        leanh::lean_inc_n(v_a_5139_, 2);
        leanh::lean_dec_ref_known(v___x_5138_, 1);
        v___f_5140_ = leanh::lean_alloc_closure(
            l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__1___boxed
                as *mut core::ffi::c_void,
            18,
            12,
        );
        leanh::lean_closure_set(v___f_5140_, 0, v___x_5117_);
        leanh::lean_closure_set(v___f_5140_, 1, v___x_5120_);
        leanh::lean_closure_set(v___f_5140_, 2, v_a_5139_);
        leanh::lean_closure_set(v___f_5140_, 3, v_ctors_5121_);
        leanh::lean_closure_set(v___f_5140_, 4, v___x_5132_);
        leanh::lean_closure_set(v___f_5140_, 5, v_ctorIdx_5124_);
        leanh::lean_closure_set(v___f_5140_, 6, v_tail_5119_);
        leanh::lean_closure_set(v___f_5140_, 7, v___x_5116_);
        leanh::lean_closure_set(v___f_5140_, 8, v___x_5122_);
        leanh::lean_closure_set(v___f_5140_, 9, v_name_5123_);
        leanh::lean_closure_set(v___f_5140_, 10, v___x_5115_);
        leanh::lean_closure_set(v___f_5140_, 11, v___x_5133_);
        v___x_5141_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__1;
        v___x_5142_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___redArg(v___x_5141_, v_a_5139_, v___f_5140_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_);
        return v___x_5142_;
    } else {
        leanh::lean_dec_ref(v___x_5133_);
        leanh::lean_dec_ref(v___x_5132_);
        leanh::lean_dec_ref(v_ctorIdx_5124_);
        leanh::lean_dec(v_name_5123_);
        leanh::lean_dec(v___x_5122_);
        leanh::lean_dec(v_ctors_5121_);
        leanh::lean_dec_ref(v___x_5120_);
        leanh::lean_dec(v_tail_5119_);
        leanh::lean_dec_ref(v___x_5117_);
        leanh::lean_dec_ref(v___x_5116_);
        leanh::lean_dec(v___x_5115_);
        return v___x_5138_;
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2___boxed(
    mut v___x_5143_: *mut leanh::LeanObject,
    mut v___x_5144_: *mut leanh::LeanObject,
    mut v___x_5145_: *mut leanh::LeanObject,
    mut v___x_5146_: *mut leanh::LeanObject,
    mut v_indName_5147_: *mut leanh::LeanObject,
    mut v_tail_5148_: *mut leanh::LeanObject,
    mut v___x_5149_: *mut leanh::LeanObject,
    mut v_ctors_5150_: *mut leanh::LeanObject,
    mut v___x_5151_: *mut leanh::LeanObject,
    mut v_name_5152_: *mut leanh::LeanObject,
    mut v_ctorIdx_5153_: *mut leanh::LeanObject,
    mut v___y_5154_: *mut leanh::LeanObject,
    mut v___y_5155_: *mut leanh::LeanObject,
    mut v___y_5156_: *mut leanh::LeanObject,
    mut v___y_5157_: *mut leanh::LeanObject,
    mut v___y_5158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5159_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2(
        v___x_5143_,
        v___x_5144_,
        v___x_5145_,
        v___x_5146_,
        v_indName_5147_,
        v_tail_5148_,
        v___x_5149_,
        v_ctors_5150_,
        v___x_5151_,
        v_name_5152_,
        v_ctorIdx_5153_,
        v___y_5154_,
        v___y_5155_,
        v___y_5156_,
        v___y_5157_,
    );
    leanh::lean_dec(v___y_5157_);
    leanh::lean_dec_ref(v___y_5156_);
    leanh::lean_dec(v___y_5155_);
    leanh::lean_dec_ref(v___y_5154_);
    return v_res_5159_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3(
    mut v_val_5160_: *mut leanh::LeanObject,
    mut v___x_5161_: *mut leanh::LeanObject,
    mut v___x_5162_: *mut leanh::LeanObject,
    mut v___x_5163_: *mut leanh::LeanObject,
    mut v_indName_5164_: *mut leanh::LeanObject,
    mut v_tail_5165_: *mut leanh::LeanObject,
    mut v_name_5166_: *mut leanh::LeanObject,
    mut v___x_5167_: *mut leanh::LeanObject,
    mut v_xs_5168_: *mut leanh::LeanObject,
    mut v_x_5169_: *mut leanh::LeanObject,
    mut v___y_5170_: *mut leanh::LeanObject,
    mut v___y_5171_: *mut leanh::LeanObject,
    mut v___y_5172_: *mut leanh::LeanObject,
    mut v___y_5173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_numParams_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_5176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_5177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_numParams_5175_ = leanh::lean_ctor_get(v_val_5160_, 1);
    leanh::lean_inc_n(v_numParams_5175_, 2);
    v_numIndices_5176_ = leanh::lean_ctor_get(v_val_5160_, 2);
    leanh::lean_inc(v_numIndices_5176_);
    v_ctors_5177_ = leanh::lean_ctor_get(v_val_5160_, 4);
    leanh::lean_inc(v_ctors_5177_);
    leanh::lean_dec_ref(v_val_5160_);
    v___x_5178_ = leanh::lean_unsigned_to_nat(0);
    leanh::lean_inc_ref_n(v_xs_5168_, 2);
    v___x_5179_ = l_Array_toSubarray___redArg(v_xs_5168_, v___x_5178_, v_numParams_5175_);
    v___x_5180_ = l_Subarray_copy___redArg(v___x_5179_);
    v___x_5181_ = lean_array_get(v___x_5161_, v_xs_5168_, v_numParams_5175_);
    v___x_5182_ = leanh::lean_unsigned_to_nat(1);
    v___x_5183_ = lean_nat_add(v_numParams_5175_, v___x_5182_);
    leanh::lean_dec(v_numParams_5175_);
    v___x_5184_ = lean_nat_add(v___x_5183_, v_numIndices_5176_);
    leanh::lean_dec(v_numIndices_5176_);
    leanh::lean_inc(v___x_5184_);
    v___x_5185_ = l_Array_toSubarray___redArg(v_xs_5168_, v___x_5183_, v___x_5184_);
    v___x_5186_ = l_Subarray_copy___redArg(v___x_5185_);
    v___x_5187_ = lean_array_get(v___x_5161_, v_xs_5168_, v___x_5184_);
    leanh::lean_dec(v___x_5184_);
    leanh::lean_dec_ref(v_xs_5168_);
    v___x_5188_ = lean_array_push(v___x_5186_, v___x_5187_);
    v___f_5189_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__2___boxed
            as *mut core::ffi::c_void,
        16,
        10,
    );
    leanh::lean_closure_set(v___f_5189_, 0, v___x_5162_);
    leanh::lean_closure_set(v___f_5189_, 1, v___x_5163_);
    leanh::lean_closure_set(v___f_5189_, 2, v___x_5180_);
    leanh::lean_closure_set(v___f_5189_, 3, v___x_5181_);
    leanh::lean_closure_set(v___f_5189_, 4, v_indName_5164_);
    leanh::lean_closure_set(v___f_5189_, 5, v_tail_5165_);
    leanh::lean_closure_set(v___f_5189_, 6, v___x_5188_);
    leanh::lean_closure_set(v___f_5189_, 7, v_ctors_5177_);
    leanh::lean_closure_set(v___f_5189_, 8, v___x_5178_);
    leanh::lean_closure_set(v___f_5189_, 9, v_name_5166_);
    v___x_5190_ =
        l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__1;
    v___x_5191_ =
        l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___lam__1___closed__3;
    v___x_5192_ = l_Lean_mkConst(v___x_5191_, v___x_5167_);
    v___x_5193_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___redArg(v___x_5190_, v___x_5192_, v___f_5189_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_);
    return v___x_5193_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3___boxed(
    mut v_val_5194_: *mut leanh::LeanObject,
    mut v___x_5195_: *mut leanh::LeanObject,
    mut v___x_5196_: *mut leanh::LeanObject,
    mut v___x_5197_: *mut leanh::LeanObject,
    mut v_indName_5198_: *mut leanh::LeanObject,
    mut v_tail_5199_: *mut leanh::LeanObject,
    mut v_name_5200_: *mut leanh::LeanObject,
    mut v___x_5201_: *mut leanh::LeanObject,
    mut v_xs_5202_: *mut leanh::LeanObject,
    mut v_x_5203_: *mut leanh::LeanObject,
    mut v___y_5204_: *mut leanh::LeanObject,
    mut v___y_5205_: *mut leanh::LeanObject,
    mut v___y_5206_: *mut leanh::LeanObject,
    mut v___y_5207_: *mut leanh::LeanObject,
    mut v___y_5208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5209_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3(
        v_val_5194_,
        v___x_5195_,
        v___x_5196_,
        v___x_5197_,
        v_indName_5198_,
        v_tail_5199_,
        v_name_5200_,
        v___x_5201_,
        v_xs_5202_,
        v_x_5203_,
        v___y_5204_,
        v___y_5205_,
        v___y_5206_,
        v___y_5207_,
    );
    leanh::lean_dec(v___y_5207_);
    leanh::lean_dec_ref(v___y_5206_);
    leanh::lean_dec(v___y_5205_);
    leanh::lean_dec_ref(v___y_5204_);
    leanh::lean_dec_ref(v_x_5203_);
    leanh::lean_dec_ref(v___x_5195_);
    return v_res_5209_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__0(
    mut v_a_5210_: *mut leanh::LeanObject,
    mut v_a_5211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5217_: u8 = 0;
    let mut v___x_5218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5223_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_5210_) == 0 {
                    v___x_5212_ = l_List_reverse___redArg(v_a_5211_);
                    return v___x_5212_;
                } else {
                    v_head_5213_ = leanh::lean_ctor_get(v_a_5210_, 0);
                    v_tail_5214_ = leanh::lean_ctor_get(v_a_5210_, 1);
                    v_isSharedCheck_5223_ = (!leanh::lean_is_exclusive(v_a_5210_)) as u8;
                    if v_isSharedCheck_5223_ == 0 {
                        v___x_5216_ = v_a_5210_;
                        v_isShared_5217_ = v_isSharedCheck_5223_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5214_);
                        leanh::lean_inc(v_head_5213_);
                        leanh::lean_dec(v_a_5210_);
                        v___x_5216_ = leanh::lean_box(0);
                        v_isShared_5217_ = v_isSharedCheck_5223_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5218_ = l_Lean_mkLevelParam(v_head_5213_);
                if v_isShared_5217_ == 0 {
                    leanh::lean_ctor_set(v___x_5216_, 1, v_a_5211_);
                    leanh::lean_ctor_set(v___x_5216_, 0, v___x_5218_);
                    v___x_5220_ = v___x_5216_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5222_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 0, v___x_5218_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5222_, 1, v_a_5211_);
                    v___x_5220_ = v_reuseFailAlloc_5222_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_5210_ = v_tail_5214_;
                v_a_5211_ = v___x_5220_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5226_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__1;
    v___x_5227_ = leanh::lean_unsigned_to_nat(58);
    v___x_5228_ = leanh::lean_unsigned_to_nat(113);
    v___x_5229_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__0;
    v___x_5230_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0;
    v___x_5231_ = l_mkPanicMessageWithDecl(
        v___x_5230_,
        v___x_5229_,
        v___x_5228_,
        v___x_5227_,
        v___x_5226_,
    );
    return v___x_5231_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5232_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__1;
    v___x_5233_ = leanh::lean_unsigned_to_nat(60);
    v___x_5234_ = leanh::lean_unsigned_to_nat(109);
    v___x_5235_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__0;
    v___x_5236_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0;
    v___x_5237_ = l_mkPanicMessageWithDecl(
        v___x_5236_,
        v___x_5235_,
        v___x_5234_,
        v___x_5233_,
        v___x_5232_,
    );
    return v___x_5237_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim(
    mut v_indName_5238_: *mut leanh::LeanObject,
    mut v_a_5239_: *mut leanh::LeanObject,
    mut v_a_5240_: *mut leanh::LeanObject,
    mut v_a_5241_: *mut leanh::LeanObject,
    mut v_a_5242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_5251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_5252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: u8 = 0;
    let mut v___x_5260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5270_: u8 = 0;
    let mut v___x_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: u8 = 0;
    let mut v___x_5274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5286_: u8 = 0;
    let mut v___x_5287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5299_: u8 = 0;
    let mut v___x_5300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5315_: u8 = 0;
    let mut v___x_5316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5327_: u8 = 0;
    let mut v___x_5329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5342_: u8 = 0;
    let mut v___x_5343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5354_: u8 = 0;
    let mut v___x_5356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5360_: u8 = 0;
    let mut v_unused_5361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5363_: u8 = 0;
    let mut v_unused_5364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5366_: u8 = 0;
    let mut v_unused_5367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5369_: u8 = 0;
    let mut v_unused_5370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5372_: u8 = 0;
    let mut v_unused_5373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5375_: u8 = 0;
    let mut v_unused_5376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5378_: u8 = 0;
    let mut v_a_5379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5382_: u8 = 0;
    let mut v___x_5384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5386_: u8 = 0;
    let mut v_a_5387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5390_: u8 = 0;
    let mut v___x_5392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5394_: u8 = 0;
    let mut v___x_5395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5400_: u8 = 0;
    let mut v___x_5402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5404_: u8 = 0;
    let mut v___x_5405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5410_: u8 = 0;
    let mut v___x_5412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5414_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_indName_5238_);
                v___x_5244_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_indName_5238_, v_a_5239_, v_a_5240_, v_a_5241_, v_a_5242_);
                if leanh::lean_obj_tag(v___x_5244_) == 0 {
                    v_a_5245_ = leanh::lean_ctor_get(v___x_5244_, 0);
                    leanh::lean_inc(v_a_5245_);
                    leanh::lean_dec_ref_known(v___x_5244_, 1);
                    if leanh::lean_obj_tag(v_a_5245_) == 5 {
                        v_val_5246_ = leanh::lean_ctor_get(v_a_5245_, 0);
                        leanh::lean_inc_ref(v_val_5246_);
                        leanh::lean_dec_ref_known(v_a_5245_, 1);
                        leanh::lean_inc_n(v_indName_5238_, 2);
                        v___x_5247_ =
                            l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName(
                                v_indName_5238_,
                            );
                        v___x_5248_ = l_Lean_mkCasesOnName(v_indName_5238_);
                        v___x_5249_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1(v___x_5248_, v_a_5239_, v_a_5240_, v_a_5241_, v_a_5242_);
                        if leanh::lean_obj_tag(v___x_5249_) == 0 {
                            v_a_5250_ = leanh::lean_ctor_get(v___x_5249_, 0);
                            leanh::lean_inc(v_a_5250_);
                            leanh::lean_dec_ref_known(v___x_5249_, 1);
                            v_name_5251_ = leanh::lean_ctor_get(v_a_5250_, 0);
                            leanh::lean_inc(v_name_5251_);
                            v_levelParams_5252_ = leanh::lean_ctor_get(v_a_5250_, 1);
                            leanh::lean_inc_n(v_levelParams_5252_, 2);
                            v_type_5253_ = leanh::lean_ctor_get(v_a_5250_, 2);
                            leanh::lean_inc_ref(v_type_5253_);
                            leanh::lean_dec(v_a_5250_);
                            v___x_5254_ = leanh::lean_box(0);
                            v___x_5255_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__0(v_levelParams_5252_, v___x_5254_);
                            if leanh::lean_obj_tag(v___x_5255_) == 1 {
                                v_tail_5256_ = leanh::lean_ctor_get(v___x_5255_, 1);
                                leanh::lean_inc(v_tail_5256_);
                                v___x_5257_ = l_Lean_instInhabitedExpr;
                                leanh::lean_inc(v_indName_5238_);
                                v___f_5258_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___lam__3___boxed as *mut core::ffi::c_void, 15, 8);
                                leanh::lean_closure_set(v___f_5258_, 0, v_val_5246_);
                                leanh::lean_closure_set(v___f_5258_, 1, v___x_5257_);
                                leanh::lean_closure_set(v___f_5258_, 2, v___x_5247_);
                                leanh::lean_closure_set(v___f_5258_, 3, v___x_5255_);
                                leanh::lean_closure_set(v___f_5258_, 4, v_indName_5238_);
                                leanh::lean_closure_set(v___f_5258_, 5, v_tail_5256_);
                                leanh::lean_closure_set(v___f_5258_, 6, v_name_5251_);
                                leanh::lean_closure_set(v___f_5258_, 7, v___x_5254_);
                                v___x_5259_ = 0;
                                v___x_5260_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_5253_, v___f_5258_, v___x_5259_, v_a_5239_, v_a_5240_, v_a_5241_, v_a_5242_);
                                if leanh::lean_obj_tag(v___x_5260_) == 0 {
                                    v_a_5261_ = leanh::lean_ctor_get(v___x_5260_, 0);
                                    leanh::lean_inc_n(v_a_5261_, 2);
                                    leanh::lean_dec_ref_known(v___x_5260_, 1);
                                    leanh::lean_inc(v_a_5242_);
                                    leanh::lean_inc_ref(v_a_5241_);
                                    leanh::lean_inc(v_a_5240_);
                                    leanh::lean_inc_ref(v_a_5239_);
                                    v___x_5262_ = lean_infer_type(
                                        v_a_5261_, v_a_5239_, v_a_5240_, v_a_5241_, v_a_5242_,
                                    );
                                    if leanh::lean_obj_tag(v___x_5262_) == 0 {
                                        v_a_5263_ = leanh::lean_ctor_get(v___x_5262_, 0);
                                        leanh::lean_inc(v_a_5263_);
                                        leanh::lean_dec_ref_known(v___x_5262_, 1);
                                        v___x_5264_ = l_Lean_mkCtorElimName(v_indName_5238_);
                                        v___x_5265_ = leanh::lean_box(1);
                                        leanh::lean_inc(v___x_5264_);
                                        v___x_5266_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v___x_5264_, v_levelParams_5252_, v_a_5263_, v_a_5261_, v___x_5265_, v_a_5242_);
                                        v_a_5267_ = leanh::lean_ctor_get(v___x_5266_, 0);
                                        v_isSharedCheck_5378_ =
                                            (!leanh::lean_is_exclusive(v___x_5266_)) as u8;
                                        if v_isSharedCheck_5378_ == 0 {
                                            v___x_5269_ = v___x_5266_;
                                            v_isShared_5270_ = v_isSharedCheck_5378_;
                                            state = 1;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_5267_);
                                            leanh::lean_dec(v___x_5266_);
                                            v___x_5269_ = leanh::lean_box(0);
                                            v_isShared_5270_ = v_isSharedCheck_5378_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v_a_5261_);
                                        leanh::lean_dec(v_levelParams_5252_);
                                        leanh::lean_dec(v_indName_5238_);
                                        v_a_5379_ = leanh::lean_ctor_get(v___x_5262_, 0);
                                        v_isSharedCheck_5386_ =
                                            (!leanh::lean_is_exclusive(v___x_5262_)) as u8;
                                        if v_isSharedCheck_5386_ == 0 {
                                            v___x_5381_ = v___x_5262_;
                                            v_isShared_5382_ = v_isSharedCheck_5386_;
                                            state = 15;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_5379_);
                                            leanh::lean_dec(v___x_5262_);
                                            v___x_5381_ = leanh::lean_box(0);
                                            v_isShared_5382_ = v_isSharedCheck_5386_;
                                            state = 15;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v_levelParams_5252_);
                                    leanh::lean_dec(v_indName_5238_);
                                    v_a_5387_ = leanh::lean_ctor_get(v___x_5260_, 0);
                                    v_isSharedCheck_5394_ =
                                        (!leanh::lean_is_exclusive(v___x_5260_)) as u8;
                                    if v_isSharedCheck_5394_ == 0 {
                                        v___x_5389_ = v___x_5260_;
                                        v_isShared_5390_ = v_isSharedCheck_5394_;
                                        state = 17;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_5387_);
                                        leanh::lean_dec(v___x_5260_);
                                        v___x_5389_ = leanh::lean_box(0);
                                        v_isShared_5390_ = v_isSharedCheck_5394_;
                                        state = 17;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec(v___x_5255_);
                                leanh::lean_dec_ref(v_type_5253_);
                                leanh::lean_dec(v_levelParams_5252_);
                                leanh::lean_dec(v_name_5251_);
                                leanh::lean_dec(v___x_5247_);
                                leanh::lean_dec_ref(v_val_5246_);
                                leanh::lean_dec(v_indName_5238_);
                                v___x_5395_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2_once), _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__2);
                                v___x_5396_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_5395_, v_a_5239_, v_a_5240_, v_a_5241_, v_a_5242_);
                                return v___x_5396_;
                            }
                        } else {
                            leanh::lean_dec(v___x_5247_);
                            leanh::lean_dec_ref(v_val_5246_);
                            leanh::lean_dec(v_indName_5238_);
                            v_a_5397_ = leanh::lean_ctor_get(v___x_5249_, 0);
                            v_isSharedCheck_5404_ =
                                (!leanh::lean_is_exclusive(v___x_5249_)) as u8;
                            if v_isSharedCheck_5404_ == 0 {
                                v___x_5399_ = v___x_5249_;
                                v_isShared_5400_ = v_isSharedCheck_5404_;
                                state = 19;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5397_);
                                leanh::lean_dec(v___x_5249_);
                                v___x_5399_ = leanh::lean_box(0);
                                v_isShared_5400_ = v_isSharedCheck_5404_;
                                state = 19;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_5245_);
                        leanh::lean_dec(v_indName_5238_);
                        v___x_5405_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3_once), _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__3);
                        v___x_5406_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_5405_, v_a_5239_, v_a_5240_, v_a_5241_, v_a_5242_);
                        return v___x_5406_;
                    }
                } else {
                    leanh::lean_dec(v_indName_5238_);
                    v_a_5407_ = leanh::lean_ctor_get(v___x_5244_, 0);
                    v_isSharedCheck_5414_ = (!leanh::lean_is_exclusive(v___x_5244_)) as u8;
                    if v_isSharedCheck_5414_ == 0 {
                        v___x_5409_ = v___x_5244_;
                        v_isShared_5410_ = v_isSharedCheck_5414_;
                        state = 21;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5407_);
                        leanh::lean_dec(v___x_5244_);
                        v___x_5409_ = leanh::lean_box(0);
                        v_isShared_5410_ = v_isSharedCheck_5414_;
                        state = 21;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5270_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5269_, 1);
                    v___x_5272_ = v___x_5269_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5377_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5377_, 0, v_a_5267_);
                    v___x_5272_ = v_reuseFailAlloc_5377_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5273_ = 1;
                v___x_5274_ = l_Lean_addAndCompile(
                    v___x_5272_,
                    v___x_5273_,
                    v___x_5259_,
                    v_a_5241_,
                    v_a_5242_,
                );
                if leanh::lean_obj_tag(v___x_5274_) == 0 {
                    leanh::lean_dec_ref_known(v___x_5274_, 1);
                    v___x_5275_ = lean_st_ref_take(v_a_5242_);
                    v_env_5276_ = leanh::lean_ctor_get(v___x_5275_, 0);
                    v_nextMacroScope_5277_ = leanh::lean_ctor_get(v___x_5275_, 1);
                    v_ngen_5278_ = leanh::lean_ctor_get(v___x_5275_, 2);
                    v_auxDeclNGen_5279_ = leanh::lean_ctor_get(v___x_5275_, 3);
                    v_traceState_5280_ = leanh::lean_ctor_get(v___x_5275_, 4);
                    v_messages_5281_ = leanh::lean_ctor_get(v___x_5275_, 6);
                    v_infoState_5282_ = leanh::lean_ctor_get(v___x_5275_, 7);
                    v_snapshotTasks_5283_ = leanh::lean_ctor_get(v___x_5275_, 8);
                    v_isSharedCheck_5375_ = (!leanh::lean_is_exclusive(v___x_5275_)) as u8;
                    if v_isSharedCheck_5375_ == 0 {
                        v_unused_5376_ = leanh::lean_ctor_get(v___x_5275_, 5);
                        leanh::lean_dec(v_unused_5376_);
                        v___x_5285_ = v___x_5275_;
                        v_isShared_5286_ = v_isSharedCheck_5375_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_5283_);
                        leanh::lean_inc(v_infoState_5282_);
                        leanh::lean_inc(v_messages_5281_);
                        leanh::lean_inc(v_traceState_5280_);
                        leanh::lean_inc(v_auxDeclNGen_5279_);
                        leanh::lean_inc(v_ngen_5278_);
                        leanh::lean_inc(v_nextMacroScope_5277_);
                        leanh::lean_inc(v_env_5276_);
                        leanh::lean_dec(v___x_5275_);
                        v___x_5285_ = leanh::lean_box(0);
                        v_isShared_5286_ = v_isSharedCheck_5375_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_5264_);
                    return v___x_5274_;
                }
            }
            3 => {
                leanh::lean_inc(v___x_5264_);
                v___x_5287_ = l_Lean_markAuxRecursor(v_env_5276_, v___x_5264_);
                v___x_5288_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2);
                if v_isShared_5286_ == 0 {
                    leanh::lean_ctor_set(v___x_5285_, 5, v___x_5288_);
                    leanh::lean_ctor_set(v___x_5285_, 0, v___x_5287_);
                    v___x_5290_ = v___x_5285_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5374_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5374_, 0, v___x_5287_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5374_, 1, v_nextMacroScope_5277_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5374_, 2, v_ngen_5278_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5374_, 3, v_auxDeclNGen_5279_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5374_, 4, v_traceState_5280_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5374_, 5, v___x_5288_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5374_, 6, v_messages_5281_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5374_, 7, v_infoState_5282_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5374_, 8, v_snapshotTasks_5283_);
                    v___x_5290_ = v_reuseFailAlloc_5374_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5291_ = lean_st_ref_set(v_a_5242_, v___x_5290_);
                v___x_5292_ = lean_st_ref_take(v_a_5240_);
                v_mctx_5293_ = leanh::lean_ctor_get(v___x_5292_, 0);
                v_zetaDeltaFVarIds_5294_ = leanh::lean_ctor_get(v___x_5292_, 2);
                v_postponed_5295_ = leanh::lean_ctor_get(v___x_5292_, 3);
                v_diag_5296_ = leanh::lean_ctor_get(v___x_5292_, 4);
                v_isSharedCheck_5372_ = (!leanh::lean_is_exclusive(v___x_5292_)) as u8;
                if v_isSharedCheck_5372_ == 0 {
                    v_unused_5373_ = leanh::lean_ctor_get(v___x_5292_, 1);
                    leanh::lean_dec(v_unused_5373_);
                    v___x_5298_ = v___x_5292_;
                    v_isShared_5299_ = v_isSharedCheck_5372_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_5296_);
                    leanh::lean_inc(v_postponed_5295_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_5294_);
                    leanh::lean_inc(v_mctx_5293_);
                    leanh::lean_dec(v___x_5292_);
                    v___x_5298_ = leanh::lean_box(0);
                    v_isShared_5299_ = v_isSharedCheck_5372_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5300_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3);
                if v_isShared_5299_ == 0 {
                    leanh::lean_ctor_set(v___x_5298_, 1, v___x_5300_);
                    v___x_5302_ = v___x_5298_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5371_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5371_, 0, v_mctx_5293_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5371_, 1, v___x_5300_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5371_,
                        2,
                        v_zetaDeltaFVarIds_5294_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5371_, 3, v_postponed_5295_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5371_, 4, v_diag_5296_);
                    v___x_5302_ = v_reuseFailAlloc_5371_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5303_ = lean_st_ref_set(v_a_5240_, v___x_5302_);
                v___x_5304_ = lean_st_ref_take(v_a_5242_);
                v_env_5305_ = leanh::lean_ctor_get(v___x_5304_, 0);
                v_nextMacroScope_5306_ = leanh::lean_ctor_get(v___x_5304_, 1);
                v_ngen_5307_ = leanh::lean_ctor_get(v___x_5304_, 2);
                v_auxDeclNGen_5308_ = leanh::lean_ctor_get(v___x_5304_, 3);
                v_traceState_5309_ = leanh::lean_ctor_get(v___x_5304_, 4);
                v_messages_5310_ = leanh::lean_ctor_get(v___x_5304_, 6);
                v_infoState_5311_ = leanh::lean_ctor_get(v___x_5304_, 7);
                v_snapshotTasks_5312_ = leanh::lean_ctor_get(v___x_5304_, 8);
                v_isSharedCheck_5369_ = (!leanh::lean_is_exclusive(v___x_5304_)) as u8;
                if v_isSharedCheck_5369_ == 0 {
                    v_unused_5370_ = leanh::lean_ctor_get(v___x_5304_, 5);
                    leanh::lean_dec(v_unused_5370_);
                    v___x_5314_ = v___x_5304_;
                    v_isShared_5315_ = v_isSharedCheck_5369_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_5312_);
                    leanh::lean_inc(v_infoState_5311_);
                    leanh::lean_inc(v_messages_5310_);
                    leanh::lean_inc(v_traceState_5309_);
                    leanh::lean_inc(v_auxDeclNGen_5308_);
                    leanh::lean_inc(v_ngen_5307_);
                    leanh::lean_inc(v_nextMacroScope_5306_);
                    leanh::lean_inc(v_env_5305_);
                    leanh::lean_dec(v___x_5304_);
                    v___x_5314_ = leanh::lean_box(0);
                    v_isShared_5315_ = v_isSharedCheck_5369_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                leanh::lean_inc(v___x_5264_);
                v___x_5316_ = l_Lean_Meta_addToCompletionBlackList(v_env_5305_, v___x_5264_);
                if v_isShared_5315_ == 0 {
                    leanh::lean_ctor_set(v___x_5314_, 5, v___x_5288_);
                    leanh::lean_ctor_set(v___x_5314_, 0, v___x_5316_);
                    v___x_5318_ = v___x_5314_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5368_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5368_, 0, v___x_5316_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5368_, 1, v_nextMacroScope_5306_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5368_, 2, v_ngen_5307_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5368_, 3, v_auxDeclNGen_5308_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5368_, 4, v_traceState_5309_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5368_, 5, v___x_5288_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5368_, 6, v_messages_5310_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5368_, 7, v_infoState_5311_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5368_, 8, v_snapshotTasks_5312_);
                    v___x_5318_ = v_reuseFailAlloc_5368_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5319_ = lean_st_ref_set(v_a_5242_, v___x_5318_);
                v___x_5320_ = lean_st_ref_take(v_a_5240_);
                v_mctx_5321_ = leanh::lean_ctor_get(v___x_5320_, 0);
                v_zetaDeltaFVarIds_5322_ = leanh::lean_ctor_get(v___x_5320_, 2);
                v_postponed_5323_ = leanh::lean_ctor_get(v___x_5320_, 3);
                v_diag_5324_ = leanh::lean_ctor_get(v___x_5320_, 4);
                v_isSharedCheck_5366_ = (!leanh::lean_is_exclusive(v___x_5320_)) as u8;
                if v_isSharedCheck_5366_ == 0 {
                    v_unused_5367_ = leanh::lean_ctor_get(v___x_5320_, 1);
                    leanh::lean_dec(v_unused_5367_);
                    v___x_5326_ = v___x_5320_;
                    v_isShared_5327_ = v_isSharedCheck_5366_;
                    state = 9;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_5324_);
                    leanh::lean_inc(v_postponed_5323_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_5322_);
                    leanh::lean_inc(v_mctx_5321_);
                    leanh::lean_dec(v___x_5320_);
                    v___x_5326_ = leanh::lean_box(0);
                    v_isShared_5327_ = v_isSharedCheck_5366_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_5327_ == 0 {
                    leanh::lean_ctor_set(v___x_5326_, 1, v___x_5300_);
                    v___x_5329_ = v___x_5326_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5365_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5365_, 0, v_mctx_5321_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5365_, 1, v___x_5300_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5365_,
                        2,
                        v_zetaDeltaFVarIds_5322_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5365_, 3, v_postponed_5323_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5365_, 4, v_diag_5324_);
                    v___x_5329_ = v_reuseFailAlloc_5365_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_5330_ = lean_st_ref_set(v_a_5240_, v___x_5329_);
                v___x_5331_ = lean_st_ref_take(v_a_5242_);
                v_env_5332_ = leanh::lean_ctor_get(v___x_5331_, 0);
                v_nextMacroScope_5333_ = leanh::lean_ctor_get(v___x_5331_, 1);
                v_ngen_5334_ = leanh::lean_ctor_get(v___x_5331_, 2);
                v_auxDeclNGen_5335_ = leanh::lean_ctor_get(v___x_5331_, 3);
                v_traceState_5336_ = leanh::lean_ctor_get(v___x_5331_, 4);
                v_messages_5337_ = leanh::lean_ctor_get(v___x_5331_, 6);
                v_infoState_5338_ = leanh::lean_ctor_get(v___x_5331_, 7);
                v_snapshotTasks_5339_ = leanh::lean_ctor_get(v___x_5331_, 8);
                v_isSharedCheck_5363_ = (!leanh::lean_is_exclusive(v___x_5331_)) as u8;
                if v_isSharedCheck_5363_ == 0 {
                    v_unused_5364_ = leanh::lean_ctor_get(v___x_5331_, 5);
                    leanh::lean_dec(v_unused_5364_);
                    v___x_5341_ = v___x_5331_;
                    v_isShared_5342_ = v_isSharedCheck_5363_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_5339_);
                    leanh::lean_inc(v_infoState_5338_);
                    leanh::lean_inc(v_messages_5337_);
                    leanh::lean_inc(v_traceState_5336_);
                    leanh::lean_inc(v_auxDeclNGen_5335_);
                    leanh::lean_inc(v_ngen_5334_);
                    leanh::lean_inc(v_nextMacroScope_5333_);
                    leanh::lean_inc(v_env_5332_);
                    leanh::lean_dec(v___x_5331_);
                    v___x_5341_ = leanh::lean_box(0);
                    v_isShared_5342_ = v_isSharedCheck_5363_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                leanh::lean_inc(v___x_5264_);
                v___x_5343_ = l_Lean_addProtected(v_env_5332_, v___x_5264_);
                if v_isShared_5342_ == 0 {
                    leanh::lean_ctor_set(v___x_5341_, 5, v___x_5288_);
                    leanh::lean_ctor_set(v___x_5341_, 0, v___x_5343_);
                    v___x_5345_ = v___x_5341_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5362_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5362_, 0, v___x_5343_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5362_, 1, v_nextMacroScope_5333_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5362_, 2, v_ngen_5334_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5362_, 3, v_auxDeclNGen_5335_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5362_, 4, v_traceState_5336_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5362_, 5, v___x_5288_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5362_, 6, v_messages_5337_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5362_, 7, v_infoState_5338_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5362_, 8, v_snapshotTasks_5339_);
                    v___x_5345_ = v_reuseFailAlloc_5362_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_5346_ = lean_st_ref_set(v_a_5242_, v___x_5345_);
                v___x_5347_ = lean_st_ref_take(v_a_5240_);
                v_mctx_5348_ = leanh::lean_ctor_get(v___x_5347_, 0);
                v_zetaDeltaFVarIds_5349_ = leanh::lean_ctor_get(v___x_5347_, 2);
                v_postponed_5350_ = leanh::lean_ctor_get(v___x_5347_, 3);
                v_diag_5351_ = leanh::lean_ctor_get(v___x_5347_, 4);
                v_isSharedCheck_5360_ = (!leanh::lean_is_exclusive(v___x_5347_)) as u8;
                if v_isSharedCheck_5360_ == 0 {
                    v_unused_5361_ = leanh::lean_ctor_get(v___x_5347_, 1);
                    leanh::lean_dec(v_unused_5361_);
                    v___x_5353_ = v___x_5347_;
                    v_isShared_5354_ = v_isSharedCheck_5360_;
                    state = 13;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_5351_);
                    leanh::lean_inc(v_postponed_5350_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_5349_);
                    leanh::lean_inc(v_mctx_5348_);
                    leanh::lean_dec(v___x_5347_);
                    v___x_5353_ = leanh::lean_box(0);
                    v_isShared_5354_ = v_isSharedCheck_5360_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_5354_ == 0 {
                    leanh::lean_ctor_set(v___x_5353_, 1, v___x_5300_);
                    v___x_5356_ = v___x_5353_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5359_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5359_, 0, v_mctx_5348_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5359_, 1, v___x_5300_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5359_,
                        2,
                        v_zetaDeltaFVarIds_5349_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5359_, 3, v_postponed_5350_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5359_, 4, v_diag_5351_);
                    v___x_5356_ = v_reuseFailAlloc_5359_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_5357_ = lean_st_ref_set(v_a_5240_, v___x_5356_);
                v___x_5358_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(v___x_5264_, v_a_5239_, v_a_5240_, v_a_5241_, v_a_5242_);
                return v___x_5358_;
            }
            15 => {
                if v_isShared_5382_ == 0 {
                    v___x_5384_ = v___x_5381_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5385_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5385_, 0, v_a_5379_);
                    v___x_5384_ = v_reuseFailAlloc_5385_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5384_;
            }
            17 => {
                if v_isShared_5390_ == 0 {
                    v___x_5392_ = v___x_5389_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5393_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5393_, 0, v_a_5387_);
                    v___x_5392_ = v_reuseFailAlloc_5393_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5392_;
            }
            19 => {
                if v_isShared_5400_ == 0 {
                    v___x_5402_ = v___x_5399_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5403_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5403_, 0, v_a_5397_);
                    v___x_5402_ = v_reuseFailAlloc_5403_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5402_;
            }
            21 => {
                if v_isShared_5410_ == 0 {
                    v___x_5412_ = v___x_5409_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5413_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5413_, 0, v_a_5407_);
                    v___x_5412_ = v_reuseFailAlloc_5413_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_5412_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___boxed(
    mut v_indName_5415_: *mut leanh::LeanObject,
    mut v_a_5416_: *mut leanh::LeanObject,
    mut v_a_5417_: *mut leanh::LeanObject,
    mut v_a_5418_: *mut leanh::LeanObject,
    mut v_a_5419_: *mut leanh::LeanObject,
    mut v_a_5420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5421_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim(
        v_indName_5415_,
        v_a_5416_,
        v_a_5417_,
        v_a_5418_,
        v_a_5419_,
    );
    leanh::lean_dec(v_a_5419_);
    leanh::lean_dec_ref(v_a_5418_);
    leanh::lean_dec(v_a_5417_);
    leanh::lean_dec_ref(v_a_5416_);
    return v_res_5421_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1(
    mut v___x_5422_: *mut leanh::LeanObject,
    mut v_k_5423_: *mut leanh::LeanObject,
    mut v_ctorIdx_5424_: *mut leanh::LeanObject,
    mut v_tail_5425_: *mut leanh::LeanObject,
    mut v___x_5426_: *mut leanh::LeanObject,
    mut v_as_5427_: *mut leanh::LeanObject,
    mut v_i_5428_: *mut leanh::LeanObject,
    mut v_j_5429_: *mut leanh::LeanObject,
    mut v_inv_5430_: *mut leanh::LeanObject,
    mut v_bs_5431_: *mut leanh::LeanObject,
    mut v___y_5432_: *mut leanh::LeanObject,
    mut v___y_5433_: *mut leanh::LeanObject,
    mut v___y_5434_: *mut leanh::LeanObject,
    mut v___y_5435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5437_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg(v___x_5422_, v_k_5423_, v_ctorIdx_5424_, v_tail_5425_, v___x_5426_, v_as_5427_, v_i_5428_, v_j_5429_, v_bs_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_);
    return v___x_5437_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___boxed(
    mut v___x_5438_: *mut leanh::LeanObject,
    mut v_k_5439_: *mut leanh::LeanObject,
    mut v_ctorIdx_5440_: *mut leanh::LeanObject,
    mut v_tail_5441_: *mut leanh::LeanObject,
    mut v___x_5442_: *mut leanh::LeanObject,
    mut v_as_5443_: *mut leanh::LeanObject,
    mut v_i_5444_: *mut leanh::LeanObject,
    mut v_j_5445_: *mut leanh::LeanObject,
    mut v_inv_5446_: *mut leanh::LeanObject,
    mut v_bs_5447_: *mut leanh::LeanObject,
    mut v___y_5448_: *mut leanh::LeanObject,
    mut v___y_5449_: *mut leanh::LeanObject,
    mut v___y_5450_: *mut leanh::LeanObject,
    mut v___y_5451_: *mut leanh::LeanObject,
    mut v___y_5452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5453_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1(v___x_5438_, v_k_5439_, v_ctorIdx_5440_, v_tail_5441_, v___x_5442_, v_as_5443_, v_i_5444_, v_j_5445_, v_inv_5446_, v_bs_5447_, v___y_5448_, v___y_5449_, v___y_5450_, v___y_5451_);
    leanh::lean_dec(v___y_5451_);
    leanh::lean_dec_ref(v___y_5450_);
    leanh::lean_dec(v___y_5449_);
    leanh::lean_dec_ref(v___y_5448_);
    leanh::lean_dec_ref(v_as_5443_);
    leanh::lean_dec_ref(v___x_5442_);
    return v_res_5453_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1(
    mut v___x_5454_: *mut leanh::LeanObject,
    mut v___x_5455_: *mut leanh::LeanObject,
    mut v___x_5456_: *mut leanh::LeanObject,
    mut v___x_5457_: *mut leanh::LeanObject,
    mut v___x_5458_: *mut leanh::LeanObject,
    mut v___x_5459_: *mut leanh::LeanObject,
    mut v___f_5460_: *mut leanh::LeanObject,
    mut v___x_5461_: *mut leanh::LeanObject,
    mut v___x_5462_: *mut leanh::LeanObject,
    mut v___y_5463_: *mut leanh::LeanObject,
    mut v___x_5464_: u8,
    mut v_h_5465_: *mut leanh::LeanObject,
    mut v___y_5466_: *mut leanh::LeanObject,
    mut v___y_5467_: *mut leanh::LeanObject,
    mut v___y_5468_: *mut leanh::LeanObject,
    mut v___y_5469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5471_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_h_5465_);
    v___x_5471_ = l_Lean_Meta_mkEqSymm(
        v_h_5465_,
        v___y_5466_,
        v___y_5467_,
        v___y_5468_,
        v___y_5469_,
    );
    if leanh::lean_obj_tag(v___x_5471_) == 0 {
        let mut v_a_5472_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5473_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5474_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5475_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5476_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5477_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5478_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5479_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5480_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5481_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_5472_ = leanh::lean_ctor_get(v___x_5471_, 0);
        leanh::lean_inc(v_a_5472_);
        leanh::lean_dec_ref_known(v___x_5471_, 1);
        leanh::lean_inc(v___x_5455_);
        v___x_5473_ = l_Lean_mkConst(v___x_5454_, v___x_5455_);
        v___x_5474_ = l_Lean_mkAppN(v___x_5473_, v___x_5456_);
        leanh::lean_inc_ref_n(v___x_5457_, 2);
        v___x_5475_ = l_Lean_Expr_app___override(v___x_5474_, v___x_5457_);
        leanh::lean_inc_ref(v___x_5458_);
        v___x_5476_ = l_Lean_Expr_app___override(v___x_5475_, v___x_5458_);
        v___x_5477_ = l_Lean_mkConst(v___x_5459_, v___x_5455_);
        leanh::lean_inc_ref(v___x_5456_);
        v___x_5478_ = lean_array_push(v___x_5456_, v___x_5457_);
        v___x_5479_ = lean_array_push(v___x_5478_, v___x_5458_);
        v___x_5480_ = l_Lean_mkAppN(v___x_5477_, v___x_5479_);
        leanh::lean_dec_ref(v___x_5479_);
        v___x_5481_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp(
            v___x_5480_,
            v___f_5460_,
            v___y_5466_,
            v___y_5467_,
            v___y_5468_,
            v___y_5469_,
        );
        if leanh::lean_obj_tag(v___x_5481_) == 0 {
            let mut v_a_5482_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5483_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5484_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5485_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5486_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5487_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5488_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5489_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5490_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5491_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5492_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5493_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5494_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5495_: u8 = 0;
            let mut v___x_5496_: u8 = 0;
            let mut v___x_5497_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_5482_ = leanh::lean_ctor_get(v___x_5481_, 0);
            leanh::lean_inc(v_a_5482_);
            leanh::lean_dec_ref_known(v___x_5481_, 1);
            v___x_5483_ = l_Lean_mkAppN(v___x_5476_, v___x_5461_);
            v___x_5484_ = l_Lean_Expr_app___override(v___x_5483_, v_a_5472_);
            v___x_5485_ = l_Lean_Expr_app___override(v___x_5484_, v_a_5482_);
            v___x_5486_ = lean_mk_empty_array_with_capacity(v___x_5462_);
            v___x_5487_ = lean_array_push(v___x_5486_, v___x_5457_);
            v___x_5488_ = l_Array_append___redArg(v___x_5456_, v___x_5487_);
            leanh::lean_dec_ref(v___x_5487_);
            v___x_5489_ = l_Array_append___redArg(v___x_5488_, v___x_5461_);
            v___x_5490_ = leanh::lean_unsigned_to_nat(2);
            v___x_5491_ = lean_mk_empty_array_with_capacity(v___x_5490_);
            v___x_5492_ = lean_array_push(v___x_5491_, v_h_5465_);
            v___x_5493_ = lean_array_push(v___x_5492_, v___y_5463_);
            v___x_5494_ = l_Array_append___redArg(v___x_5489_, v___x_5493_);
            leanh::lean_dec_ref(v___x_5493_);
            v___x_5495_ = 0;
            v___x_5496_ = 1;
            v___x_5497_ = l_Lean_Meta_mkLambdaFVars(
                v___x_5494_,
                v___x_5485_,
                v___x_5495_,
                v___x_5464_,
                v___x_5495_,
                v___x_5464_,
                v___x_5496_,
                v___y_5466_,
                v___y_5467_,
                v___y_5468_,
                v___y_5469_,
            );
            leanh::lean_dec_ref(v___x_5494_);
            return v___x_5497_;
        } else {
            leanh::lean_dec_ref(v___x_5476_);
            leanh::lean_dec(v_a_5472_);
            leanh::lean_dec_ref(v_h_5465_);
            leanh::lean_dec_ref(v___y_5463_);
            leanh::lean_dec_ref(v___x_5457_);
            leanh::lean_dec_ref(v___x_5456_);
            return v___x_5481_;
        }
    } else {
        leanh::lean_dec_ref(v_h_5465_);
        leanh::lean_dec_ref(v___y_5463_);
        leanh::lean_dec_ref(v___f_5460_);
        leanh::lean_dec(v___x_5459_);
        leanh::lean_dec_ref(v___x_5458_);
        leanh::lean_dec_ref(v___x_5457_);
        leanh::lean_dec_ref(v___x_5456_);
        leanh::lean_dec(v___x_5455_);
        leanh::lean_dec(v___x_5454_);
        return v___x_5471_;
    }
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5498_: *mut leanh::LeanObject = *_args.add(0);
    let mut v___x_5499_: *mut leanh::LeanObject = *_args.add(1);
    let mut v___x_5500_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___x_5501_: *mut leanh::LeanObject = *_args.add(3);
    let mut v___x_5502_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___x_5503_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___f_5504_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_5505_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___x_5506_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_5507_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___x_5508_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_h_5509_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_5510_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_5511_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_5512_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_5513_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_5514_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___x_9833__boxed_5515_: u8 = 0;
    let mut v_res_5516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9833__boxed_5515_ = (leanh::lean_unbox(v___x_5508_) as u8);
    v_res_5516_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1(v___x_5498_, v___x_5499_, v___x_5500_, v___x_5501_, v___x_5502_, v___x_5503_, v___f_5504_, v___x_5505_, v___x_5506_, v___y_5507_, v___x_9833__boxed_5515_, v_h_5509_, v___y_5510_, v___y_5511_, v___y_5512_, v___y_5513_);
    leanh::lean_dec(v___y_5513_);
    leanh::lean_dec_ref(v___y_5512_);
    leanh::lean_dec(v___y_5511_);
    leanh::lean_dec_ref(v___y_5510_);
    leanh::lean_dec(v___x_5506_);
    leanh::lean_dec_ref(v___x_5505_);
    return v_res_5516_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0(
    mut v___y_5517_: *mut leanh::LeanObject,
    mut v_x_5518_: *mut leanh::LeanObject,
    mut v___y_5519_: *mut leanh::LeanObject,
    mut v___y_5520_: *mut leanh::LeanObject,
    mut v___y_5521_: *mut leanh::LeanObject,
    mut v___y_5522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5524_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5524_, 0, v___y_5517_);
    return v___x_5524_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0___boxed(
    mut v___y_5525_: *mut leanh::LeanObject,
    mut v_x_5526_: *mut leanh::LeanObject,
    mut v___y_5527_: *mut leanh::LeanObject,
    mut v___y_5528_: *mut leanh::LeanObject,
    mut v___y_5529_: *mut leanh::LeanObject,
    mut v___y_5530_: *mut leanh::LeanObject,
    mut v___y_5531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5532_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0(v___y_5525_, v_x_5526_, v___y_5527_, v___y_5528_, v___y_5529_, v___y_5530_);
    leanh::lean_dec(v___y_5530_);
    leanh::lean_dec_ref(v___y_5529_);
    leanh::lean_dec(v___y_5528_);
    leanh::lean_dec_ref(v___y_5527_);
    leanh::lean_dec_ref(v_x_5526_);
    return v_res_5532_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2(
    mut v_val_5533_: *mut leanh::LeanObject,
    mut v___x_5534_: *mut leanh::LeanObject,
    mut v___x_5535_: *mut leanh::LeanObject,
    mut v___x_5536_: *mut leanh::LeanObject,
    mut v_indName_5537_: *mut leanh::LeanObject,
    mut v_tail_5538_: *mut leanh::LeanObject,
    mut v_i_5539_: *mut leanh::LeanObject,
    mut v___x_5540_: *mut leanh::LeanObject,
    mut v___x_5541_: *mut leanh::LeanObject,
    mut v___x_5542_: *mut leanh::LeanObject,
    mut v___x_5543_: u8,
    mut v_xs_5544_: *mut leanh::LeanObject,
    mut v_x_5545_: *mut leanh::LeanObject,
    mut v___y_5546_: *mut leanh::LeanObject,
    mut v___y_5547_: *mut leanh::LeanObject,
    mut v___y_5548_: *mut leanh::LeanObject,
    mut v___y_5549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_numParams_5551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_5552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_5562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_5563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: u8 = 0;
    let mut v___x_5583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_numParams_5551_ = leanh::lean_ctor_get(v_val_5533_, 1);
                leanh::lean_inc_n(v_numParams_5551_, 2);
                v_numIndices_5552_ = leanh::lean_ctor_get(v_val_5533_, 2);
                leanh::lean_inc(v_numIndices_5552_);
                leanh::lean_dec_ref(v_val_5533_);
                leanh::lean_inc_ref_n(v_xs_5544_, 2);
                v___x_5553_ =
                    l_Array_toSubarray___redArg(v_xs_5544_, v___x_5534_, v_numParams_5551_);
                v___x_5554_ = lean_array_get(v___x_5535_, v_xs_5544_, v_numParams_5551_);
                v___x_5555_ = lean_nat_add(v_numParams_5551_, v___x_5536_);
                leanh::lean_dec(v_numParams_5551_);
                v___x_5556_ = lean_nat_add(v___x_5555_, v_numIndices_5552_);
                leanh::lean_dec(v_numIndices_5552_);
                leanh::lean_inc(v___x_5556_);
                v___x_5557_ = l_Array_toSubarray___redArg(v_xs_5544_, v___x_5555_, v___x_5556_);
                v___x_5558_ = lean_array_get(v___x_5535_, v_xs_5544_, v___x_5556_);
                v___x_5559_ = lean_nat_add(v___x_5556_, v___x_5536_);
                leanh::lean_dec(v___x_5556_);
                v___x_5560_ = lean_array_get_size(v_xs_5544_);
                v___x_5561_ = l_Array_toSubarray___redArg(v_xs_5544_, v___x_5559_, v___x_5560_);
                v_start_5562_ = leanh::lean_ctor_get(v___x_5561_, 1);
                leanh::lean_inc(v_start_5562_);
                v_stop_5563_ = leanh::lean_ctor_get(v___x_5561_, 2);
                leanh::lean_inc(v_stop_5563_);
                v___x_5564_ = l_Subarray_copy___redArg(v___x_5553_);
                v___x_5565_ = l_Subarray_copy___redArg(v___x_5557_);
                v___x_5566_ = lean_array_push(v___x_5565_, v___x_5558_);
                v___x_5581_ = lean_nat_sub(v_stop_5563_, v_start_5562_);
                leanh::lean_dec(v_start_5562_);
                leanh::lean_dec(v_stop_5563_);
                v___x_5582_ = lean_nat_dec_lt(v_i_5539_, v___x_5581_);
                leanh::lean_dec(v___x_5581_);
                if v___x_5582_ == 0 {
                    leanh::lean_dec_ref(v___x_5561_);
                    v___x_5583_ = l_outOfBounds___redArg(v___x_5535_);
                    v___y_5568_ = v___x_5583_;
                    state = 1;
                    continue;
                } else {
                    v___x_5584_ = l_Subarray_get___redArg(v___x_5561_, v_i_5539_);
                    leanh::lean_dec_ref(v___x_5561_);
                    v___y_5568_ = v___x_5584_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5569_ = l_mkCtorIdxName(v_indName_5537_);
                v___x_5570_ = l_Lean_mkConst(v___x_5569_, v_tail_5538_);
                leanh::lean_inc_ref(v___x_5564_);
                v___x_5571_ = l_Array_append___redArg(v___x_5564_, v___x_5566_);
                v___x_5572_ = l_Lean_mkAppN(v___x_5570_, v___x_5571_);
                leanh::lean_dec_ref(v___x_5571_);
                v___x_5573_ = l_Lean_mkRawNatLit(v_i_5539_);
                leanh::lean_inc_ref(v___x_5573_);
                v___x_5574_ = l_Lean_Meta_mkEq(
                    v___x_5572_,
                    v___x_5573_,
                    v___y_5546_,
                    v___y_5547_,
                    v___y_5548_,
                    v___y_5549_,
                );
                if leanh::lean_obj_tag(v___x_5574_) == 0 {
                    v_a_5575_ = leanh::lean_ctor_get(v___x_5574_, 0);
                    leanh::lean_inc(v_a_5575_);
                    leanh::lean_dec_ref_known(v___x_5574_, 1);
                    leanh::lean_inc_ref(v___y_5568_);
                    v___f_5576_ = leanh::lean_alloc_closure(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                    leanh::lean_closure_set(v___f_5576_, 0, v___y_5568_);
                    v___x_5577_ = leanh::lean_box((v___x_5543_) as usize);
                    v___f_5578_ = leanh::lean_alloc_closure(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__1___boxed as *mut core::ffi::c_void, 17, 11);
                    leanh::lean_closure_set(v___f_5578_, 0, v___x_5540_);
                    leanh::lean_closure_set(v___f_5578_, 1, v___x_5541_);
                    leanh::lean_closure_set(v___f_5578_, 2, v___x_5564_);
                    leanh::lean_closure_set(v___f_5578_, 3, v___x_5554_);
                    leanh::lean_closure_set(v___f_5578_, 4, v___x_5573_);
                    leanh::lean_closure_set(v___f_5578_, 5, v___x_5542_);
                    leanh::lean_closure_set(v___f_5578_, 6, v___f_5576_);
                    leanh::lean_closure_set(v___f_5578_, 7, v___x_5566_);
                    leanh::lean_closure_set(v___f_5578_, 8, v___x_5536_);
                    leanh::lean_closure_set(v___f_5578_, 9, v___y_5568_);
                    leanh::lean_closure_set(v___f_5578_, 10, v___x_5577_);
                    v___x_5579_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__1___redArg___closed__1;
                    v___x_5580_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__3___redArg(v___x_5579_, v_a_5575_, v___f_5578_, v___y_5546_, v___y_5547_, v___y_5548_, v___y_5549_);
                    return v___x_5580_;
                } else {
                    leanh::lean_dec_ref(v___x_5573_);
                    leanh::lean_dec_ref(v___y_5568_);
                    leanh::lean_dec_ref(v___x_5566_);
                    leanh::lean_dec_ref(v___x_5564_);
                    leanh::lean_dec(v___x_5554_);
                    leanh::lean_dec(v___x_5542_);
                    leanh::lean_dec(v___x_5541_);
                    leanh::lean_dec(v___x_5540_);
                    leanh::lean_dec(v___x_5536_);
                    return v___x_5574_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_5585_: *mut leanh::LeanObject = *_args.add(0);
    let mut v___x_5586_: *mut leanh::LeanObject = *_args.add(1);
    let mut v___x_5587_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___x_5588_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_indName_5589_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_tail_5590_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_i_5591_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_5592_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___x_5593_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___x_5594_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___x_5595_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_xs_5596_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_x_5597_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_5598_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_5599_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_5600_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_5601_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_5602_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___x_9961__boxed_5603_: u8 = 0;
    let mut v_res_5604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9961__boxed_5603_ = (leanh::lean_unbox(v___x_5595_) as u8);
    v_res_5604_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2(v_val_5585_, v___x_5586_, v___x_5587_, v___x_5588_, v_indName_5589_, v_tail_5590_, v_i_5591_, v___x_5592_, v___x_5593_, v___x_5594_, v___x_9961__boxed_5603_, v_xs_5596_, v_x_5597_, v___y_5598_, v___y_5599_, v___y_5600_, v___y_5601_);
    leanh::lean_dec(v___y_5601_);
    leanh::lean_dec_ref(v___y_5600_);
    leanh::lean_dec(v___y_5599_);
    leanh::lean_dec_ref(v___y_5598_);
    leanh::lean_dec_ref(v_x_5597_);
    leanh::lean_dec_ref(v___x_5587_);
    return v_res_5604_;
}
pub unsafe fn _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5606_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__0;
    v___x_5607_ = l_Lean_stringToMessageData(v___x_5606_);
    return v___x_5607_;
}
pub unsafe fn _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5609_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__2;
    v___x_5610_ = l_Lean_stringToMessageData(v___x_5609_);
    return v___x_5610_;
}
pub unsafe fn _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_5612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5612_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__4;
    v___x_5613_ = l_Lean_stringToMessageData(v___x_5612_);
    return v___x_5613_;
}
pub unsafe fn l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg(
    mut v_attrName_5614_: *mut leanh::LeanObject,
    mut v_declName_5615_: *mut leanh::LeanObject,
    mut v___y_5616_: *mut leanh::LeanObject,
    mut v___y_5617_: *mut leanh::LeanObject,
    mut v___y_5618_: *mut leanh::LeanObject,
    mut v___y_5619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5626_: u8 = 0;
    let mut v___x_5627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5621_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1);
    v___x_5622_ = l_Lean_MessageData_ofName(v_attrName_5614_);
    v___x_5623_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5623_, 0, v___x_5621_);
    leanh::lean_ctor_set(v___x_5623_, 1, v___x_5622_);
    v___x_5624_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3);
    v___x_5625_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5625_, 0, v___x_5623_);
    leanh::lean_ctor_set(v___x_5625_, 1, v___x_5624_);
    v___x_5626_ = 0;
    v___x_5627_ = l_Lean_MessageData_ofConstName(v_declName_5615_, v___x_5626_);
    v___x_5628_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5628_, 0, v___x_5625_);
    leanh::lean_ctor_set(v___x_5628_, 1, v___x_5627_);
    v___x_5629_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5_once), _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__5);
    v___x_5630_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5630_, 0, v___x_5628_);
    leanh::lean_ctor_set(v___x_5630_, 1, v___x_5629_);
    v___x_5631_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_5630_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_);
    return v___x_5631_;
}
pub unsafe fn l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___boxed(
    mut v_attrName_5632_: *mut leanh::LeanObject,
    mut v_declName_5633_: *mut leanh::LeanObject,
    mut v___y_5634_: *mut leanh::LeanObject,
    mut v___y_5635_: *mut leanh::LeanObject,
    mut v___y_5636_: *mut leanh::LeanObject,
    mut v___y_5637_: *mut leanh::LeanObject,
    mut v___y_5638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5639_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg(v_attrName_5632_, v_declName_5633_, v___y_5634_, v___y_5635_, v___y_5636_, v___y_5637_);
    leanh::lean_dec(v___y_5637_);
    leanh::lean_dec_ref(v___y_5636_);
    leanh::lean_dec(v___y_5635_);
    leanh::lean_dec_ref(v___y_5634_);
    return v_res_5639_;
}
pub unsafe fn _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5641_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__0;
    v___x_5642_ = l_Lean_stringToMessageData(v___x_5641_);
    return v___x_5642_;
}
pub unsafe fn _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5644_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__2;
    v___x_5645_ = l_Lean_stringToMessageData(v___x_5644_);
    return v___x_5645_;
}
pub unsafe fn l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg(
    mut v_attrName_5646_: *mut leanh::LeanObject,
    mut v_declName_5647_: *mut leanh::LeanObject,
    mut v_asyncPrefix_x3f_5648_: *mut leanh::LeanObject,
    mut v___y_5649_: *mut leanh::LeanObject,
    mut v___y_5650_: *mut leanh::LeanObject,
    mut v___y_5651_: *mut leanh::LeanObject,
    mut v___y_5652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: u8 = 0;
    let mut v___x_5662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_asyncPrefix_x3f_5648_) == 0 {
                    v___x_5668_ = l_Lean_MessageData_nil;
                    v___y_5655_ = v___x_5668_;
                    state = 1;
                    continue;
                } else {
                    v_val_5669_ = leanh::lean_ctor_get(v_asyncPrefix_x3f_5648_, 0);
                    leanh::lean_inc(v_val_5669_);
                    leanh::lean_dec_ref_known(v_asyncPrefix_x3f_5648_, 1);
                    v___x_5670_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3_once), _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__3);
                    v___x_5671_ = l_Lean_MessageData_ofName(v_val_5669_);
                    v___x_5672_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5672_, 0, v___x_5670_);
                    leanh::lean_ctor_set(v___x_5672_, 1, v___x_5671_);
                    v___x_5673_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3);
                    v___x_5674_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5674_, 0, v___x_5672_);
                    leanh::lean_ctor_set(v___x_5674_, 1, v___x_5673_);
                    v___y_5655_ = v___x_5674_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5656_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__1);
                v___x_5657_ = l_Lean_MessageData_ofName(v_attrName_5646_);
                v___x_5658_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5658_, 0, v___x_5656_);
                leanh::lean_ctor_set(v___x_5658_, 1, v___x_5657_);
                v___x_5659_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg___closed__3);
                v___x_5660_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5660_, 0, v___x_5658_);
                leanh::lean_ctor_set(v___x_5660_, 1, v___x_5659_);
                v___x_5661_ = 0;
                v___x_5662_ = l_Lean_MessageData_ofConstName(v_declName_5647_, v___x_5661_);
                v___x_5663_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5663_, 0, v___x_5660_);
                leanh::lean_ctor_set(v___x_5663_, 1, v___x_5662_);
                v___x_5664_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___closed__1);
                v___x_5665_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5665_, 0, v___x_5663_);
                leanh::lean_ctor_set(v___x_5665_, 1, v___x_5664_);
                v___x_5666_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5666_, 0, v___x_5665_);
                leanh::lean_ctor_set(v___x_5666_, 1, v___y_5655_);
                v___x_5667_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_5666_, v___y_5649_, v___y_5650_, v___y_5651_, v___y_5652_);
                return v___x_5667_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg___boxed(
    mut v_attrName_5675_: *mut leanh::LeanObject,
    mut v_declName_5676_: *mut leanh::LeanObject,
    mut v_asyncPrefix_x3f_5677_: *mut leanh::LeanObject,
    mut v___y_5678_: *mut leanh::LeanObject,
    mut v___y_5679_: *mut leanh::LeanObject,
    mut v___y_5680_: *mut leanh::LeanObject,
    mut v___y_5681_: *mut leanh::LeanObject,
    mut v___y_5682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5683_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg(v_attrName_5675_, v_declName_5676_, v_asyncPrefix_x3f_5677_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_);
    leanh::lean_dec(v___y_5681_);
    leanh::lean_dec_ref(v___y_5680_);
    leanh::lean_dec(v___y_5679_);
    leanh::lean_dec_ref(v___y_5678_);
    return v_res_5683_;
}
pub unsafe fn l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0(
    mut v_attr_5684_: *mut leanh::LeanObject,
    mut v_decl_5685_: *mut leanh::LeanObject,
    mut v___y_5686_: *mut leanh::LeanObject,
    mut v___y_5687_: *mut leanh::LeanObject,
    mut v___y_5688_: *mut leanh::LeanObject,
    mut v___y_5689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_5695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_5696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5707_: u8 = 0;
    let mut v_asyncMode_5708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5721_: u8 = 0;
    let mut v___x_5722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5729_: u8 = 0;
    let mut v_unused_5730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5732_: u8 = 0;
    let mut v_unused_5733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_5741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_5742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_attr_5743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_5744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: u8 = 0;
    let mut v_toAttributeImplCore_5746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_5747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_attr_5751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toAttributeImplCore_5752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_5753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5734_ = lean_st_ref_get(v___y_5689_);
                v_env_5735_ = leanh::lean_ctor_get(v___x_5734_, 0);
                leanh::lean_inc_ref(v_env_5735_);
                leanh::lean_dec(v___x_5734_);
                v___x_5750_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_5735_, v_decl_5685_);
                if leanh::lean_obj_tag(v___x_5750_) == 0 {
                    v___y_5737_ = v___y_5686_;
                    v___y_5738_ = v___y_5687_;
                    v___y_5739_ = v___y_5688_;
                    v___y_5740_ = v___y_5689_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v___x_5750_, 1);
                    leanh::lean_dec_ref(v_env_5735_);
                    v_attr_5751_ = leanh::lean_ctor_get(v_attr_5684_, 0);
                    leanh::lean_inc_ref(v_attr_5751_);
                    leanh::lean_dec_ref(v_attr_5684_);
                    v_toAttributeImplCore_5752_ = leanh::lean_ctor_get(v_attr_5751_, 0);
                    leanh::lean_inc_ref(v_toAttributeImplCore_5752_);
                    leanh::lean_dec_ref(v_attr_5751_);
                    v_name_5753_ = leanh::lean_ctor_get(v_toAttributeImplCore_5752_, 1);
                    leanh::lean_inc(v_name_5753_);
                    leanh::lean_dec_ref(v_toAttributeImplCore_5752_);
                    v___x_5754_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg(v_name_5753_, v_decl_5685_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_);
                    return v___x_5754_;
                }
            }
            1 => {
                v___x_5694_ = lean_st_ref_take(v___y_5693_);
                v_ext_5695_ = leanh::lean_ctor_get(v_attr_5684_, 1);
                leanh::lean_inc_ref(v_ext_5695_);
                leanh::lean_dec_ref(v_attr_5684_);
                v_toEnvExtension_5696_ = leanh::lean_ctor_get(v_ext_5695_, 0);
                v_env_5697_ = leanh::lean_ctor_get(v___x_5694_, 0);
                v_nextMacroScope_5698_ = leanh::lean_ctor_get(v___x_5694_, 1);
                v_ngen_5699_ = leanh::lean_ctor_get(v___x_5694_, 2);
                v_auxDeclNGen_5700_ = leanh::lean_ctor_get(v___x_5694_, 3);
                v_traceState_5701_ = leanh::lean_ctor_get(v___x_5694_, 4);
                v_messages_5702_ = leanh::lean_ctor_get(v___x_5694_, 6);
                v_infoState_5703_ = leanh::lean_ctor_get(v___x_5694_, 7);
                v_snapshotTasks_5704_ = leanh::lean_ctor_get(v___x_5694_, 8);
                v_isSharedCheck_5732_ = (!leanh::lean_is_exclusive(v___x_5694_)) as u8;
                if v_isSharedCheck_5732_ == 0 {
                    v_unused_5733_ = leanh::lean_ctor_get(v___x_5694_, 5);
                    leanh::lean_dec(v_unused_5733_);
                    v___x_5706_ = v___x_5694_;
                    v_isShared_5707_ = v_isSharedCheck_5732_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_5704_);
                    leanh::lean_inc(v_infoState_5703_);
                    leanh::lean_inc(v_messages_5702_);
                    leanh::lean_inc(v_traceState_5701_);
                    leanh::lean_inc(v_auxDeclNGen_5700_);
                    leanh::lean_inc(v_ngen_5699_);
                    leanh::lean_inc(v_nextMacroScope_5698_);
                    leanh::lean_inc(v_env_5697_);
                    leanh::lean_dec(v___x_5694_);
                    v___x_5706_ = leanh::lean_box(0);
                    v_isShared_5707_ = v_isSharedCheck_5732_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_5708_ = leanh::lean_ctor_get(v_toEnvExtension_5696_, 2);
                leanh::lean_inc(v_asyncMode_5708_);
                leanh::lean_inc(v_decl_5685_);
                v___x_5709_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v_ext_5695_,
                    v_env_5697_,
                    v_decl_5685_,
                    v_asyncMode_5708_,
                    v_decl_5685_,
                );
                leanh::lean_dec(v_asyncMode_5708_);
                v___x_5710_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2);
                if v_isShared_5707_ == 0 {
                    leanh::lean_ctor_set(v___x_5706_, 5, v___x_5710_);
                    leanh::lean_ctor_set(v___x_5706_, 0, v___x_5709_);
                    v___x_5712_ = v___x_5706_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5731_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5731_, 0, v___x_5709_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5731_, 1, v_nextMacroScope_5698_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5731_, 2, v_ngen_5699_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5731_, 3, v_auxDeclNGen_5700_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5731_, 4, v_traceState_5701_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5731_, 5, v___x_5710_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5731_, 6, v_messages_5702_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5731_, 7, v_infoState_5703_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5731_, 8, v_snapshotTasks_5704_);
                    v___x_5712_ = v_reuseFailAlloc_5731_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5713_ = lean_st_ref_set(v___y_5693_, v___x_5712_);
                v___x_5714_ = lean_st_ref_take(v___y_5692_);
                v_mctx_5715_ = leanh::lean_ctor_get(v___x_5714_, 0);
                v_zetaDeltaFVarIds_5716_ = leanh::lean_ctor_get(v___x_5714_, 2);
                v_postponed_5717_ = leanh::lean_ctor_get(v___x_5714_, 3);
                v_diag_5718_ = leanh::lean_ctor_get(v___x_5714_, 4);
                v_isSharedCheck_5729_ = (!leanh::lean_is_exclusive(v___x_5714_)) as u8;
                if v_isSharedCheck_5729_ == 0 {
                    v_unused_5730_ = leanh::lean_ctor_get(v___x_5714_, 1);
                    leanh::lean_dec(v_unused_5730_);
                    v___x_5720_ = v___x_5714_;
                    v_isShared_5721_ = v_isSharedCheck_5729_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_5718_);
                    leanh::lean_inc(v_postponed_5717_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_5716_);
                    leanh::lean_inc(v_mctx_5715_);
                    leanh::lean_dec(v___x_5714_);
                    v___x_5720_ = leanh::lean_box(0);
                    v_isShared_5721_ = v_isSharedCheck_5729_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5722_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3);
                if v_isShared_5721_ == 0 {
                    leanh::lean_ctor_set(v___x_5720_, 1, v___x_5722_);
                    v___x_5724_ = v___x_5720_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5728_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5728_, 0, v_mctx_5715_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5728_, 1, v___x_5722_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5728_,
                        2,
                        v_zetaDeltaFVarIds_5716_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5728_, 3, v_postponed_5717_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5728_, 4, v_diag_5718_);
                    v___x_5724_ = v_reuseFailAlloc_5728_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5725_ = lean_st_ref_set(v___y_5692_, v___x_5724_);
                v___x_5726_ = leanh::lean_box(0);
                v___x_5727_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5727_, 0, v___x_5726_);
                return v___x_5727_;
            }
            6 => {
                v_ext_5741_ = leanh::lean_ctor_get(v_attr_5684_, 1);
                v_toEnvExtension_5742_ = leanh::lean_ctor_get(v_ext_5741_, 0);
                v_attr_5743_ = leanh::lean_ctor_get(v_attr_5684_, 0);
                v_asyncMode_5744_ = leanh::lean_ctor_get(v_toEnvExtension_5742_, 2);
                leanh::lean_inc(v_decl_5685_);
                leanh::lean_inc_ref(v_env_5735_);
                v___x_5745_ = l_Lean_EnvExtension_asyncMayModify___redArg(
                    v_env_5735_,
                    v_decl_5685_,
                    v_asyncMode_5744_,
                );
                if v___x_5745_ == 0 {
                    leanh::lean_inc_ref(v_attr_5743_);
                    leanh::lean_dec_ref(v_attr_5684_);
                    v_toAttributeImplCore_5746_ = leanh::lean_ctor_get(v_attr_5743_, 0);
                    leanh::lean_inc_ref(v_toAttributeImplCore_5746_);
                    leanh::lean_dec_ref(v_attr_5743_);
                    v_name_5747_ = leanh::lean_ctor_get(v_toAttributeImplCore_5746_, 1);
                    leanh::lean_inc(v_name_5747_);
                    leanh::lean_dec_ref(v_toAttributeImplCore_5746_);
                    v___x_5748_ = l_Lean_Environment_asyncPrefix_x3f(v_env_5735_);
                    v___x_5749_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg(v_name_5747_, v_decl_5685_, v___x_5748_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_);
                    return v___x_5749_;
                } else {
                    leanh::lean_dec_ref(v_env_5735_);
                    v___y_5692_ = v___y_5738_;
                    v___y_5693_ = v___y_5740_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0___boxed(
    mut v_attr_5755_: *mut leanh::LeanObject,
    mut v_decl_5756_: *mut leanh::LeanObject,
    mut v___y_5757_: *mut leanh::LeanObject,
    mut v___y_5758_: *mut leanh::LeanObject,
    mut v___y_5759_: *mut leanh::LeanObject,
    mut v___y_5760_: *mut leanh::LeanObject,
    mut v___y_5761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5762_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5762_ = l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0(v_attr_5755_, v_decl_5756_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_);
    leanh::lean_dec(v___y_5760_);
    leanh::lean_dec_ref(v___y_5759_);
    leanh::lean_dec(v___y_5758_);
    leanh::lean_dec_ref(v___y_5757_);
    return v_res_5762_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg(
    mut v_val_5763_: *mut leanh::LeanObject,
    mut v_indName_5764_: *mut leanh::LeanObject,
    mut v_tail_5765_: *mut leanh::LeanObject,
    mut v___x_5766_: *mut leanh::LeanObject,
    mut v___x_5767_: *mut leanh::LeanObject,
    mut v___x_5768_: *mut leanh::LeanObject,
    mut v_a_5769_: *mut leanh::LeanObject,
    mut v_range_5770_: *mut leanh::LeanObject,
    mut v_b_5771_: *mut leanh::LeanObject,
    mut v_i_5772_: *mut leanh::LeanObject,
    mut v___y_5773_: *mut leanh::LeanObject,
    mut v___y_5774_: *mut leanh::LeanObject,
    mut v___y_5775_: *mut leanh::LeanObject,
    mut v___y_5776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stop_5778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_step_5779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: u8 = 0;
    let mut v___x_5781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_5782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5789_: u8 = 0;
    let mut v___x_5790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_5794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5803_: u8 = 0;
    let mut v___x_5805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5818_: u8 = 0;
    let mut v___x_5819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5831_: u8 = 0;
    let mut v___x_5832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5847_: u8 = 0;
    let mut v___x_5848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5859_: u8 = 0;
    let mut v___x_5861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5874_: u8 = 0;
    let mut v___x_5875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5886_: u8 = 0;
    let mut v___x_5888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5901_: u8 = 0;
    let mut v___x_5902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5913_: u8 = 0;
    let mut v___x_5915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5924_: u8 = 0;
    let mut v_unused_5925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5927_: u8 = 0;
    let mut v_unused_5928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5930_: u8 = 0;
    let mut v_unused_5931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5933_: u8 = 0;
    let mut v_unused_5934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5936_: u8 = 0;
    let mut v_unused_5937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5939_: u8 = 0;
    let mut v_unused_5940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5942_: u8 = 0;
    let mut v_unused_5943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5945_: u8 = 0;
    let mut v_unused_5946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5948_: u8 = 0;
    let mut v_a_5949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5952_: u8 = 0;
    let mut v___x_5954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5956_: u8 = 0;
    let mut v_a_5957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5960_: u8 = 0;
    let mut v___x_5962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5964_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stop_5778_ = leanh::lean_ctor_get(v_range_5770_, 1);
                v_step_5779_ = leanh::lean_ctor_get(v_range_5770_, 2);
                v___x_5780_ = lean_nat_dec_lt(v_i_5772_, v_stop_5778_);
                if v___x_5780_ == 0 {
                    leanh::lean_dec(v_i_5772_);
                    leanh::lean_dec_ref(v_a_5769_);
                    leanh::lean_dec(v___x_5768_);
                    leanh::lean_dec(v___x_5767_);
                    leanh::lean_dec(v___x_5766_);
                    leanh::lean_dec(v_tail_5765_);
                    leanh::lean_dec(v_indName_5764_);
                    leanh::lean_dec_ref(v_val_5763_);
                    v___x_5781_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5781_, 0, v_b_5771_);
                    return v___x_5781_;
                } else {
                    v_levelParams_5782_ = leanh::lean_ctor_get(v_a_5769_, 1);
                    v_type_5783_ = leanh::lean_ctor_get(v_a_5769_, 2);
                    v___x_5784_ = leanh::lean_unsigned_to_nat(0);
                    v___x_5785_ = l_Lean_instInhabitedExpr;
                    v___x_5786_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5787_ = leanh::lean_box((v___x_5780_) as usize);
                    leanh::lean_inc(v___x_5768_);
                    leanh::lean_inc(v___x_5767_);
                    leanh::lean_inc(v___x_5766_);
                    leanh::lean_inc(v_i_5772_);
                    leanh::lean_inc(v_tail_5765_);
                    leanh::lean_inc(v_indName_5764_);
                    leanh::lean_inc_ref(v_val_5763_);
                    v___f_5788_ = leanh::lean_alloc_closure(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___lam__2___boxed as *mut core::ffi::c_void, 18, 11);
                    leanh::lean_closure_set(v___f_5788_, 0, v_val_5763_);
                    leanh::lean_closure_set(v___f_5788_, 1, v___x_5784_);
                    leanh::lean_closure_set(v___f_5788_, 2, v___x_5785_);
                    leanh::lean_closure_set(v___f_5788_, 3, v___x_5786_);
                    leanh::lean_closure_set(v___f_5788_, 4, v_indName_5764_);
                    leanh::lean_closure_set(v___f_5788_, 5, v_tail_5765_);
                    leanh::lean_closure_set(v___f_5788_, 6, v_i_5772_);
                    leanh::lean_closure_set(v___f_5788_, 7, v___x_5766_);
                    leanh::lean_closure_set(v___f_5788_, 8, v___x_5767_);
                    leanh::lean_closure_set(v___f_5788_, 9, v___x_5768_);
                    leanh::lean_closure_set(v___f_5788_, 10, v___x_5787_);
                    v___x_5789_ = 0;
                    leanh::lean_inc_ref(v_type_5783_);
                    v___x_5790_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__4___redArg(v_type_5783_, v___f_5788_, v___x_5789_, v___y_5773_, v___y_5774_, v___y_5775_, v___y_5776_);
                    if leanh::lean_obj_tag(v___x_5790_) == 0 {
                        v_a_5791_ = leanh::lean_ctor_get(v___x_5790_, 0);
                        leanh::lean_inc_n(v_a_5791_, 2);
                        leanh::lean_dec_ref_known(v___x_5790_, 1);
                        leanh::lean_inc(v___y_5776_);
                        leanh::lean_inc_ref(v___y_5775_);
                        leanh::lean_inc(v___y_5774_);
                        leanh::lean_inc_ref(v___y_5773_);
                        v___x_5792_ = lean_infer_type(
                            v_a_5791_,
                            v___y_5773_,
                            v___y_5774_,
                            v___y_5775_,
                            v___y_5776_,
                        );
                        if leanh::lean_obj_tag(v___x_5792_) == 0 {
                            v_a_5793_ = leanh::lean_ctor_get(v___x_5792_, 0);
                            leanh::lean_inc(v_a_5793_);
                            leanh::lean_dec_ref_known(v___x_5792_, 1);
                            v_ctors_5794_ = leanh::lean_ctor_get(v_val_5763_, 4);
                            v___x_5795_ = leanh::lean_box(0);
                            leanh::lean_inc(v_i_5772_);
                            v___x_5796_ = l_List_get_x21Internal___redArg(
                                v___x_5795_,
                                v_ctors_5794_,
                                v_i_5772_,
                            );
                            leanh::lean_inc(v_indName_5764_);
                            v___x_5797_ =
                                l_Lean_mkConstructorElimName(v_indName_5764_, v___x_5796_);
                            v___x_5798_ = leanh::lean_box(1);
                            leanh::lean_inc(v_levelParams_5782_);
                            leanh::lean_inc(v___x_5797_);
                            v___x_5799_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__5___redArg(v___x_5797_, v_levelParams_5782_, v_a_5793_, v_a_5791_, v___x_5798_, v___y_5776_);
                            v_a_5800_ = leanh::lean_ctor_get(v___x_5799_, 0);
                            v_isSharedCheck_5948_ =
                                (!leanh::lean_is_exclusive(v___x_5799_)) as u8;
                            if v_isSharedCheck_5948_ == 0 {
                                v___x_5802_ = v___x_5799_;
                                v_isShared_5803_ = v_isSharedCheck_5948_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5800_);
                                leanh::lean_dec(v___x_5799_);
                                v___x_5802_ = leanh::lean_box(0);
                                v_isShared_5803_ = v_isSharedCheck_5948_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_5791_);
                            leanh::lean_dec(v_i_5772_);
                            leanh::lean_dec_ref(v_a_5769_);
                            leanh::lean_dec(v___x_5768_);
                            leanh::lean_dec(v___x_5767_);
                            leanh::lean_dec(v___x_5766_);
                            leanh::lean_dec(v_tail_5765_);
                            leanh::lean_dec(v_indName_5764_);
                            leanh::lean_dec_ref(v_val_5763_);
                            v_a_5949_ = leanh::lean_ctor_get(v___x_5792_, 0);
                            v_isSharedCheck_5956_ =
                                (!leanh::lean_is_exclusive(v___x_5792_)) as u8;
                            if v_isSharedCheck_5956_ == 0 {
                                v___x_5951_ = v___x_5792_;
                                v_isShared_5952_ = v_isSharedCheck_5956_;
                                state = 19;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5949_);
                                leanh::lean_dec(v___x_5792_);
                                v___x_5951_ = leanh::lean_box(0);
                                v_isShared_5952_ = v_isSharedCheck_5956_;
                                state = 19;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_i_5772_);
                        leanh::lean_dec_ref(v_a_5769_);
                        leanh::lean_dec(v___x_5768_);
                        leanh::lean_dec(v___x_5767_);
                        leanh::lean_dec(v___x_5766_);
                        leanh::lean_dec(v_tail_5765_);
                        leanh::lean_dec(v_indName_5764_);
                        leanh::lean_dec_ref(v_val_5763_);
                        v_a_5957_ = leanh::lean_ctor_get(v___x_5790_, 0);
                        v_isSharedCheck_5964_ =
                            (!leanh::lean_is_exclusive(v___x_5790_)) as u8;
                        if v_isSharedCheck_5964_ == 0 {
                            v___x_5959_ = v___x_5790_;
                            v_isShared_5960_ = v_isSharedCheck_5964_;
                            state = 21;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5957_);
                            leanh::lean_dec(v___x_5790_);
                            v___x_5959_ = leanh::lean_box(0);
                            v_isShared_5960_ = v_isSharedCheck_5964_;
                            state = 21;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5803_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5802_, 1);
                    v___x_5805_ = v___x_5802_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5947_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5947_, 0, v_a_5800_);
                    v___x_5805_ = v_reuseFailAlloc_5947_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5806_ = l_Lean_addAndCompile(
                    v___x_5805_,
                    v___x_5780_,
                    v___x_5789_,
                    v___y_5775_,
                    v___y_5776_,
                );
                if leanh::lean_obj_tag(v___x_5806_) == 0 {
                    leanh::lean_dec_ref_known(v___x_5806_, 1);
                    v___x_5807_ = lean_st_ref_take(v___y_5776_);
                    v_env_5808_ = leanh::lean_ctor_get(v___x_5807_, 0);
                    v_nextMacroScope_5809_ = leanh::lean_ctor_get(v___x_5807_, 1);
                    v_ngen_5810_ = leanh::lean_ctor_get(v___x_5807_, 2);
                    v_auxDeclNGen_5811_ = leanh::lean_ctor_get(v___x_5807_, 3);
                    v_traceState_5812_ = leanh::lean_ctor_get(v___x_5807_, 4);
                    v_messages_5813_ = leanh::lean_ctor_get(v___x_5807_, 6);
                    v_infoState_5814_ = leanh::lean_ctor_get(v___x_5807_, 7);
                    v_snapshotTasks_5815_ = leanh::lean_ctor_get(v___x_5807_, 8);
                    v_isSharedCheck_5945_ = (!leanh::lean_is_exclusive(v___x_5807_)) as u8;
                    if v_isSharedCheck_5945_ == 0 {
                        v_unused_5946_ = leanh::lean_ctor_get(v___x_5807_, 5);
                        leanh::lean_dec(v_unused_5946_);
                        v___x_5817_ = v___x_5807_;
                        v_isShared_5818_ = v_isSharedCheck_5945_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_5815_);
                        leanh::lean_inc(v_infoState_5814_);
                        leanh::lean_inc(v_messages_5813_);
                        leanh::lean_inc(v_traceState_5812_);
                        leanh::lean_inc(v_auxDeclNGen_5811_);
                        leanh::lean_inc(v_ngen_5810_);
                        leanh::lean_inc(v_nextMacroScope_5809_);
                        leanh::lean_inc(v_env_5808_);
                        leanh::lean_dec(v___x_5807_);
                        v___x_5817_ = leanh::lean_box(0);
                        v_isShared_5818_ = v_isSharedCheck_5945_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_5797_);
                    leanh::lean_dec(v_i_5772_);
                    leanh::lean_dec_ref(v_a_5769_);
                    leanh::lean_dec(v___x_5768_);
                    leanh::lean_dec(v___x_5767_);
                    leanh::lean_dec(v___x_5766_);
                    leanh::lean_dec(v_tail_5765_);
                    leanh::lean_dec(v_indName_5764_);
                    leanh::lean_dec_ref(v_val_5763_);
                    return v___x_5806_;
                }
            }
            3 => {
                leanh::lean_inc(v___x_5797_);
                v___x_5819_ = l_Lean_markAuxRecursor(v_env_5808_, v___x_5797_);
                v___x_5820_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2);
                if v_isShared_5818_ == 0 {
                    leanh::lean_ctor_set(v___x_5817_, 5, v___x_5820_);
                    leanh::lean_ctor_set(v___x_5817_, 0, v___x_5819_);
                    v___x_5822_ = v___x_5817_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5944_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5944_, 0, v___x_5819_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5944_, 1, v_nextMacroScope_5809_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5944_, 2, v_ngen_5810_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5944_, 3, v_auxDeclNGen_5811_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5944_, 4, v_traceState_5812_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5944_, 5, v___x_5820_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5944_, 6, v_messages_5813_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5944_, 7, v_infoState_5814_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5944_, 8, v_snapshotTasks_5815_);
                    v___x_5822_ = v_reuseFailAlloc_5944_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5823_ = lean_st_ref_set(v___y_5776_, v___x_5822_);
                v___x_5824_ = lean_st_ref_take(v___y_5774_);
                v_mctx_5825_ = leanh::lean_ctor_get(v___x_5824_, 0);
                v_zetaDeltaFVarIds_5826_ = leanh::lean_ctor_get(v___x_5824_, 2);
                v_postponed_5827_ = leanh::lean_ctor_get(v___x_5824_, 3);
                v_diag_5828_ = leanh::lean_ctor_get(v___x_5824_, 4);
                v_isSharedCheck_5942_ = (!leanh::lean_is_exclusive(v___x_5824_)) as u8;
                if v_isSharedCheck_5942_ == 0 {
                    v_unused_5943_ = leanh::lean_ctor_get(v___x_5824_, 1);
                    leanh::lean_dec(v_unused_5943_);
                    v___x_5830_ = v___x_5824_;
                    v_isShared_5831_ = v_isSharedCheck_5942_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_5828_);
                    leanh::lean_inc(v_postponed_5827_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_5826_);
                    leanh::lean_inc(v_mctx_5825_);
                    leanh::lean_dec(v___x_5824_);
                    v___x_5830_ = leanh::lean_box(0);
                    v_isShared_5831_ = v_isSharedCheck_5942_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5832_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3);
                if v_isShared_5831_ == 0 {
                    leanh::lean_ctor_set(v___x_5830_, 1, v___x_5832_);
                    v___x_5834_ = v___x_5830_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5941_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5941_, 0, v_mctx_5825_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5941_, 1, v___x_5832_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5941_,
                        2,
                        v_zetaDeltaFVarIds_5826_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5941_, 3, v_postponed_5827_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5941_, 4, v_diag_5828_);
                    v___x_5834_ = v_reuseFailAlloc_5941_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5835_ = lean_st_ref_set(v___y_5774_, v___x_5834_);
                v___x_5836_ = lean_st_ref_take(v___y_5776_);
                v_env_5837_ = leanh::lean_ctor_get(v___x_5836_, 0);
                v_nextMacroScope_5838_ = leanh::lean_ctor_get(v___x_5836_, 1);
                v_ngen_5839_ = leanh::lean_ctor_get(v___x_5836_, 2);
                v_auxDeclNGen_5840_ = leanh::lean_ctor_get(v___x_5836_, 3);
                v_traceState_5841_ = leanh::lean_ctor_get(v___x_5836_, 4);
                v_messages_5842_ = leanh::lean_ctor_get(v___x_5836_, 6);
                v_infoState_5843_ = leanh::lean_ctor_get(v___x_5836_, 7);
                v_snapshotTasks_5844_ = leanh::lean_ctor_get(v___x_5836_, 8);
                v_isSharedCheck_5939_ = (!leanh::lean_is_exclusive(v___x_5836_)) as u8;
                if v_isSharedCheck_5939_ == 0 {
                    v_unused_5940_ = leanh::lean_ctor_get(v___x_5836_, 5);
                    leanh::lean_dec(v_unused_5940_);
                    v___x_5846_ = v___x_5836_;
                    v_isShared_5847_ = v_isSharedCheck_5939_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_5844_);
                    leanh::lean_inc(v_infoState_5843_);
                    leanh::lean_inc(v_messages_5842_);
                    leanh::lean_inc(v_traceState_5841_);
                    leanh::lean_inc(v_auxDeclNGen_5840_);
                    leanh::lean_inc(v_ngen_5839_);
                    leanh::lean_inc(v_nextMacroScope_5838_);
                    leanh::lean_inc(v_env_5837_);
                    leanh::lean_dec(v___x_5836_);
                    v___x_5846_ = leanh::lean_box(0);
                    v_isShared_5847_ = v_isSharedCheck_5939_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                leanh::lean_inc(v___x_5797_);
                v___x_5848_ = l_Lean_markSparseCasesOn(v_env_5837_, v___x_5797_);
                if v_isShared_5847_ == 0 {
                    leanh::lean_ctor_set(v___x_5846_, 5, v___x_5820_);
                    leanh::lean_ctor_set(v___x_5846_, 0, v___x_5848_);
                    v___x_5850_ = v___x_5846_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5938_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5938_, 0, v___x_5848_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5938_, 1, v_nextMacroScope_5838_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5938_, 2, v_ngen_5839_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5938_, 3, v_auxDeclNGen_5840_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5938_, 4, v_traceState_5841_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5938_, 5, v___x_5820_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5938_, 6, v_messages_5842_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5938_, 7, v_infoState_5843_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5938_, 8, v_snapshotTasks_5844_);
                    v___x_5850_ = v_reuseFailAlloc_5938_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5851_ = lean_st_ref_set(v___y_5776_, v___x_5850_);
                v___x_5852_ = lean_st_ref_take(v___y_5774_);
                v_mctx_5853_ = leanh::lean_ctor_get(v___x_5852_, 0);
                v_zetaDeltaFVarIds_5854_ = leanh::lean_ctor_get(v___x_5852_, 2);
                v_postponed_5855_ = leanh::lean_ctor_get(v___x_5852_, 3);
                v_diag_5856_ = leanh::lean_ctor_get(v___x_5852_, 4);
                v_isSharedCheck_5936_ = (!leanh::lean_is_exclusive(v___x_5852_)) as u8;
                if v_isSharedCheck_5936_ == 0 {
                    v_unused_5937_ = leanh::lean_ctor_get(v___x_5852_, 1);
                    leanh::lean_dec(v_unused_5937_);
                    v___x_5858_ = v___x_5852_;
                    v_isShared_5859_ = v_isSharedCheck_5936_;
                    state = 9;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_5856_);
                    leanh::lean_inc(v_postponed_5855_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_5854_);
                    leanh::lean_inc(v_mctx_5853_);
                    leanh::lean_dec(v___x_5852_);
                    v___x_5858_ = leanh::lean_box(0);
                    v_isShared_5859_ = v_isSharedCheck_5936_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_5859_ == 0 {
                    leanh::lean_ctor_set(v___x_5858_, 1, v___x_5832_);
                    v___x_5861_ = v___x_5858_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5935_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5935_, 0, v_mctx_5853_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5935_, 1, v___x_5832_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5935_,
                        2,
                        v_zetaDeltaFVarIds_5854_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5935_, 3, v_postponed_5855_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5935_, 4, v_diag_5856_);
                    v___x_5861_ = v_reuseFailAlloc_5935_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_5862_ = lean_st_ref_set(v___y_5774_, v___x_5861_);
                v___x_5863_ = lean_st_ref_take(v___y_5776_);
                v_env_5864_ = leanh::lean_ctor_get(v___x_5863_, 0);
                v_nextMacroScope_5865_ = leanh::lean_ctor_get(v___x_5863_, 1);
                v_ngen_5866_ = leanh::lean_ctor_get(v___x_5863_, 2);
                v_auxDeclNGen_5867_ = leanh::lean_ctor_get(v___x_5863_, 3);
                v_traceState_5868_ = leanh::lean_ctor_get(v___x_5863_, 4);
                v_messages_5869_ = leanh::lean_ctor_get(v___x_5863_, 6);
                v_infoState_5870_ = leanh::lean_ctor_get(v___x_5863_, 7);
                v_snapshotTasks_5871_ = leanh::lean_ctor_get(v___x_5863_, 8);
                v_isSharedCheck_5933_ = (!leanh::lean_is_exclusive(v___x_5863_)) as u8;
                if v_isSharedCheck_5933_ == 0 {
                    v_unused_5934_ = leanh::lean_ctor_get(v___x_5863_, 5);
                    leanh::lean_dec(v_unused_5934_);
                    v___x_5873_ = v___x_5863_;
                    v_isShared_5874_ = v_isSharedCheck_5933_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_5871_);
                    leanh::lean_inc(v_infoState_5870_);
                    leanh::lean_inc(v_messages_5869_);
                    leanh::lean_inc(v_traceState_5868_);
                    leanh::lean_inc(v_auxDeclNGen_5867_);
                    leanh::lean_inc(v_ngen_5866_);
                    leanh::lean_inc(v_nextMacroScope_5865_);
                    leanh::lean_inc(v_env_5864_);
                    leanh::lean_dec(v___x_5863_);
                    v___x_5873_ = leanh::lean_box(0);
                    v_isShared_5874_ = v_isSharedCheck_5933_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                leanh::lean_inc(v___x_5797_);
                v___x_5875_ = l_Lean_Meta_addToCompletionBlackList(v_env_5864_, v___x_5797_);
                if v_isShared_5874_ == 0 {
                    leanh::lean_ctor_set(v___x_5873_, 5, v___x_5820_);
                    leanh::lean_ctor_set(v___x_5873_, 0, v___x_5875_);
                    v___x_5877_ = v___x_5873_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5932_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5932_, 0, v___x_5875_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5932_, 1, v_nextMacroScope_5865_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5932_, 2, v_ngen_5866_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5932_, 3, v_auxDeclNGen_5867_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5932_, 4, v_traceState_5868_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5932_, 5, v___x_5820_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5932_, 6, v_messages_5869_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5932_, 7, v_infoState_5870_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5932_, 8, v_snapshotTasks_5871_);
                    v___x_5877_ = v_reuseFailAlloc_5932_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_5878_ = lean_st_ref_set(v___y_5776_, v___x_5877_);
                v___x_5879_ = lean_st_ref_take(v___y_5774_);
                v_mctx_5880_ = leanh::lean_ctor_get(v___x_5879_, 0);
                v_zetaDeltaFVarIds_5881_ = leanh::lean_ctor_get(v___x_5879_, 2);
                v_postponed_5882_ = leanh::lean_ctor_get(v___x_5879_, 3);
                v_diag_5883_ = leanh::lean_ctor_get(v___x_5879_, 4);
                v_isSharedCheck_5930_ = (!leanh::lean_is_exclusive(v___x_5879_)) as u8;
                if v_isSharedCheck_5930_ == 0 {
                    v_unused_5931_ = leanh::lean_ctor_get(v___x_5879_, 1);
                    leanh::lean_dec(v_unused_5931_);
                    v___x_5885_ = v___x_5879_;
                    v_isShared_5886_ = v_isSharedCheck_5930_;
                    state = 13;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_5883_);
                    leanh::lean_inc(v_postponed_5882_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_5881_);
                    leanh::lean_inc(v_mctx_5880_);
                    leanh::lean_dec(v___x_5879_);
                    v___x_5885_ = leanh::lean_box(0);
                    v_isShared_5886_ = v_isSharedCheck_5930_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_5886_ == 0 {
                    leanh::lean_ctor_set(v___x_5885_, 1, v___x_5832_);
                    v___x_5888_ = v___x_5885_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5929_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5929_, 0, v_mctx_5880_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5929_, 1, v___x_5832_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5929_,
                        2,
                        v_zetaDeltaFVarIds_5881_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5929_, 3, v_postponed_5882_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5929_, 4, v_diag_5883_);
                    v___x_5888_ = v_reuseFailAlloc_5929_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_5889_ = lean_st_ref_set(v___y_5774_, v___x_5888_);
                v___x_5890_ = lean_st_ref_take(v___y_5776_);
                v_env_5891_ = leanh::lean_ctor_get(v___x_5890_, 0);
                v_nextMacroScope_5892_ = leanh::lean_ctor_get(v___x_5890_, 1);
                v_ngen_5893_ = leanh::lean_ctor_get(v___x_5890_, 2);
                v_auxDeclNGen_5894_ = leanh::lean_ctor_get(v___x_5890_, 3);
                v_traceState_5895_ = leanh::lean_ctor_get(v___x_5890_, 4);
                v_messages_5896_ = leanh::lean_ctor_get(v___x_5890_, 6);
                v_infoState_5897_ = leanh::lean_ctor_get(v___x_5890_, 7);
                v_snapshotTasks_5898_ = leanh::lean_ctor_get(v___x_5890_, 8);
                v_isSharedCheck_5927_ = (!leanh::lean_is_exclusive(v___x_5890_)) as u8;
                if v_isSharedCheck_5927_ == 0 {
                    v_unused_5928_ = leanh::lean_ctor_get(v___x_5890_, 5);
                    leanh::lean_dec(v_unused_5928_);
                    v___x_5900_ = v___x_5890_;
                    v_isShared_5901_ = v_isSharedCheck_5927_;
                    state = 15;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_5898_);
                    leanh::lean_inc(v_infoState_5897_);
                    leanh::lean_inc(v_messages_5896_);
                    leanh::lean_inc(v_traceState_5895_);
                    leanh::lean_inc(v_auxDeclNGen_5894_);
                    leanh::lean_inc(v_ngen_5893_);
                    leanh::lean_inc(v_nextMacroScope_5892_);
                    leanh::lean_inc(v_env_5891_);
                    leanh::lean_dec(v___x_5890_);
                    v___x_5900_ = leanh::lean_box(0);
                    v_isShared_5901_ = v_isSharedCheck_5927_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                leanh::lean_inc(v___x_5797_);
                v___x_5902_ = l_Lean_addProtected(v_env_5891_, v___x_5797_);
                if v_isShared_5901_ == 0 {
                    leanh::lean_ctor_set(v___x_5900_, 5, v___x_5820_);
                    leanh::lean_ctor_set(v___x_5900_, 0, v___x_5902_);
                    v___x_5904_ = v___x_5900_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5926_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5926_, 0, v___x_5902_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5926_, 1, v_nextMacroScope_5892_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5926_, 2, v_ngen_5893_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5926_, 3, v_auxDeclNGen_5894_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5926_, 4, v_traceState_5895_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5926_, 5, v___x_5820_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5926_, 6, v_messages_5896_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5926_, 7, v_infoState_5897_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5926_, 8, v_snapshotTasks_5898_);
                    v___x_5904_ = v_reuseFailAlloc_5926_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_5905_ = lean_st_ref_set(v___y_5776_, v___x_5904_);
                v___x_5906_ = lean_st_ref_take(v___y_5774_);
                v_mctx_5907_ = leanh::lean_ctor_get(v___x_5906_, 0);
                v_zetaDeltaFVarIds_5908_ = leanh::lean_ctor_get(v___x_5906_, 2);
                v_postponed_5909_ = leanh::lean_ctor_get(v___x_5906_, 3);
                v_diag_5910_ = leanh::lean_ctor_get(v___x_5906_, 4);
                v_isSharedCheck_5924_ = (!leanh::lean_is_exclusive(v___x_5906_)) as u8;
                if v_isSharedCheck_5924_ == 0 {
                    v_unused_5925_ = leanh::lean_ctor_get(v___x_5906_, 1);
                    leanh::lean_dec(v_unused_5925_);
                    v___x_5912_ = v___x_5906_;
                    v_isShared_5913_ = v_isSharedCheck_5924_;
                    state = 17;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_5910_);
                    leanh::lean_inc(v_postponed_5909_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_5908_);
                    leanh::lean_inc(v_mctx_5907_);
                    leanh::lean_dec(v___x_5906_);
                    v___x_5912_ = leanh::lean_box(0);
                    v_isShared_5913_ = v_isSharedCheck_5924_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_5913_ == 0 {
                    leanh::lean_ctor_set(v___x_5912_, 1, v___x_5832_);
                    v___x_5915_ = v___x_5912_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5923_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5923_, 0, v_mctx_5907_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5923_, 1, v___x_5832_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5923_,
                        2,
                        v_zetaDeltaFVarIds_5908_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5923_, 3, v_postponed_5909_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5923_, 4, v_diag_5910_);
                    v___x_5915_ = v_reuseFailAlloc_5923_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_5916_ = lean_st_ref_set(v___y_5774_, v___x_5915_);
                v___x_5917_ = l_Lean_Elab_Term_elabAsElim;
                leanh::lean_inc(v___x_5797_);
                v___x_5918_ = l_Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0(v___x_5917_, v___x_5797_, v___y_5773_, v___y_5774_, v___y_5775_, v___y_5776_);
                if leanh::lean_obj_tag(v___x_5918_) == 0 {
                    leanh::lean_dec_ref_known(v___x_5918_, 1);
                    v___x_5919_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6(v___x_5797_, v___y_5773_, v___y_5774_, v___y_5775_, v___y_5776_);
                    leanh::lean_dec_ref(v___x_5919_);
                    v___x_5920_ = leanh::lean_box(0);
                    v___x_5921_ = lean_nat_add(v_i_5772_, v_step_5779_);
                    leanh::lean_dec(v_i_5772_);
                    v_b_5771_ = v___x_5920_;
                    v_i_5772_ = v___x_5921_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v___x_5797_);
                    leanh::lean_dec(v_i_5772_);
                    leanh::lean_dec_ref(v_a_5769_);
                    leanh::lean_dec(v___x_5768_);
                    leanh::lean_dec(v___x_5767_);
                    leanh::lean_dec(v___x_5766_);
                    leanh::lean_dec(v_tail_5765_);
                    leanh::lean_dec(v_indName_5764_);
                    leanh::lean_dec_ref(v_val_5763_);
                    return v___x_5918_;
                }
            }
            19 => {
                if v_isShared_5952_ == 0 {
                    v___x_5954_ = v___x_5951_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5955_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5955_, 0, v_a_5949_);
                    v___x_5954_ = v_reuseFailAlloc_5955_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5954_;
            }
            21 => {
                if v_isShared_5960_ == 0 {
                    v___x_5962_ = v___x_5959_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5963_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5963_, 0, v_a_5957_);
                    v___x_5962_ = v_reuseFailAlloc_5963_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_5962_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg___boxed(
    mut v_val_5965_: *mut leanh::LeanObject,
    mut v_indName_5966_: *mut leanh::LeanObject,
    mut v_tail_5967_: *mut leanh::LeanObject,
    mut v___x_5968_: *mut leanh::LeanObject,
    mut v___x_5969_: *mut leanh::LeanObject,
    mut v___x_5970_: *mut leanh::LeanObject,
    mut v_a_5971_: *mut leanh::LeanObject,
    mut v_range_5972_: *mut leanh::LeanObject,
    mut v_b_5973_: *mut leanh::LeanObject,
    mut v_i_5974_: *mut leanh::LeanObject,
    mut v___y_5975_: *mut leanh::LeanObject,
    mut v___y_5976_: *mut leanh::LeanObject,
    mut v___y_5977_: *mut leanh::LeanObject,
    mut v___y_5978_: *mut leanh::LeanObject,
    mut v___y_5979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5980_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5980_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg(v_val_5965_, v_indName_5966_, v_tail_5967_, v___x_5968_, v___x_5969_, v___x_5970_, v_a_5971_, v_range_5972_, v_b_5973_, v_i_5974_, v___y_5975_, v___y_5976_, v___y_5977_, v___y_5978_);
    leanh::lean_dec(v___y_5978_);
    leanh::lean_dec_ref(v___y_5977_);
    leanh::lean_dec(v___y_5976_);
    leanh::lean_dec_ref(v___y_5975_);
    leanh::lean_dec_ref(v_range_5972_);
    return v_res_5980_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5982_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim___closed__1;
    v___x_5983_ = leanh::lean_unsigned_to_nat(58);
    v___x_5984_ = leanh::lean_unsigned_to_nat(169);
    v___x_5985_ =
        l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__0;
    v___x_5986_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0;
    v___x_5987_ = l_mkPanicMessageWithDecl(
        v___x_5986_,
        v___x_5985_,
        v___x_5984_,
        v___x_5983_,
        v___x_5982_,
    );
    return v___x_5987_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5988_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType___closed__1;
    v___x_5989_ = leanh::lean_unsigned_to_nat(60);
    v___x_5990_ = leanh::lean_unsigned_to_nat(166);
    v___x_5991_ =
        l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__0;
    v___x_5992_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_maxLevels___closed__0;
    v___x_5993_ = l_mkPanicMessageWithDecl(
        v___x_5992_,
        v___x_5991_,
        v___x_5990_,
        v___x_5989_,
        v___x_5988_,
    );
    return v___x_5993_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim(
    mut v_indName_5994_: *mut leanh::LeanObject,
    mut v_a_5995_: *mut leanh::LeanObject,
    mut v_a_5996_: *mut leanh::LeanObject,
    mut v_a_5997_: *mut leanh::LeanObject,
    mut v_a_5998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_6006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6009_: u8 = 0;
    let mut v___x_6010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6026_: u8 = 0;
    let mut v___x_6028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6030_: u8 = 0;
    let mut v_unused_6031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6036_: u8 = 0;
    let mut v___x_6038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6040_: u8 = 0;
    let mut v___x_6041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6043_: u8 = 0;
    let mut v_unused_6044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6049_: u8 = 0;
    let mut v___x_6051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6053_: u8 = 0;
    let mut v___x_6054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6059_: u8 = 0;
    let mut v___x_6061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6063_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_indName_5994_);
                v___x_6000_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_indName_5994_, v_a_5995_, v_a_5996_, v_a_5997_, v_a_5998_);
                if leanh::lean_obj_tag(v___x_6000_) == 0 {
                    v_a_6001_ = leanh::lean_ctor_get(v___x_6000_, 0);
                    leanh::lean_inc(v_a_6001_);
                    leanh::lean_dec_ref_known(v___x_6000_, 1);
                    if leanh::lean_obj_tag(v_a_6001_) == 5 {
                        v_val_6002_ = leanh::lean_ctor_get(v_a_6001_, 0);
                        leanh::lean_inc_ref(v_val_6002_);
                        leanh::lean_dec_ref_known(v_a_6001_, 1);
                        leanh::lean_inc(v_indName_5994_);
                        v___x_6003_ = l_Lean_mkCasesOnName(v_indName_5994_);
                        leanh::lean_inc(v___x_6003_);
                        v___x_6004_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1(v___x_6003_, v_a_5995_, v_a_5996_, v_a_5997_, v_a_5998_);
                        if leanh::lean_obj_tag(v___x_6004_) == 0 {
                            v_a_6005_ = leanh::lean_ctor_get(v___x_6004_, 0);
                            leanh::lean_inc(v_a_6005_);
                            leanh::lean_dec_ref_known(v___x_6004_, 1);
                            v_levelParams_6006_ = leanh::lean_ctor_get(v_a_6005_, 1);
                            v_isSharedCheck_6043_ =
                                (!leanh::lean_is_exclusive(v_a_6005_)) as u8;
                            if v_isSharedCheck_6043_ == 0 {
                                v_unused_6044_ = leanh::lean_ctor_get(v_a_6005_, 2);
                                leanh::lean_dec(v_unused_6044_);
                                v_unused_6045_ = leanh::lean_ctor_get(v_a_6005_, 0);
                                leanh::lean_dec(v_unused_6045_);
                                v___x_6008_ = v_a_6005_;
                                v_isShared_6009_ = v_isSharedCheck_6043_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_levelParams_6006_);
                                leanh::lean_dec(v_a_6005_);
                                v___x_6008_ = leanh::lean_box(0);
                                v_isShared_6009_ = v_isSharedCheck_6043_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_6003_);
                            leanh::lean_dec_ref(v_val_6002_);
                            leanh::lean_dec(v_indName_5994_);
                            v_a_6046_ = leanh::lean_ctor_get(v___x_6004_, 0);
                            v_isSharedCheck_6053_ =
                                (!leanh::lean_is_exclusive(v___x_6004_)) as u8;
                            if v_isSharedCheck_6053_ == 0 {
                                v___x_6048_ = v___x_6004_;
                                v_isShared_6049_ = v_isSharedCheck_6053_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6046_);
                                leanh::lean_dec(v___x_6004_);
                                v___x_6048_ = leanh::lean_box(0);
                                v_isShared_6049_ = v_isSharedCheck_6053_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_6001_);
                        leanh::lean_dec(v_indName_5994_);
                        v___x_6054_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2_once), _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__2);
                        v___x_6055_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_6054_, v_a_5995_, v_a_5996_, v_a_5997_, v_a_5998_);
                        return v___x_6055_;
                    }
                } else {
                    leanh::lean_dec(v_indName_5994_);
                    v_a_6056_ = leanh::lean_ctor_get(v___x_6000_, 0);
                    v_isSharedCheck_6063_ = (!leanh::lean_is_exclusive(v___x_6000_)) as u8;
                    if v_isSharedCheck_6063_ == 0 {
                        v___x_6058_ = v___x_6000_;
                        v_isShared_6059_ = v_isSharedCheck_6063_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6056_);
                        leanh::lean_dec(v___x_6000_);
                        v___x_6058_ = leanh::lean_box(0);
                        v_isShared_6059_ = v_isSharedCheck_6063_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6010_ = leanh::lean_box(0);
                v___x_6011_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim_spec__0(v_levelParams_6006_, v___x_6010_);
                if leanh::lean_obj_tag(v___x_6011_) == 1 {
                    v_tail_6012_ = leanh::lean_ctor_get(v___x_6011_, 1);
                    leanh::lean_inc(v_tail_6012_);
                    v___x_6013_ = l_Lean_getConstVal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__1(v___x_6003_, v_a_5995_, v_a_5996_, v_a_5997_, v_a_5998_);
                    if leanh::lean_obj_tag(v___x_6013_) == 0 {
                        v_a_6014_ = leanh::lean_ctor_get(v___x_6013_, 0);
                        leanh::lean_inc(v_a_6014_);
                        leanh::lean_dec_ref_known(v___x_6013_, 1);
                        leanh::lean_inc_n(v_indName_5994_, 2);
                        v___x_6015_ = l_Lean_mkCtorElimName(v_indName_5994_);
                        v___x_6016_ =
                            l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimTypeName(
                                v_indName_5994_,
                            );
                        v___x_6017_ = leanh::lean_unsigned_to_nat(0);
                        v___x_6018_ = l_Lean_InductiveVal_numCtors(v_val_6002_);
                        v___x_6019_ = leanh::lean_unsigned_to_nat(1);
                        if v_isShared_6009_ == 0 {
                            leanh::lean_ctor_set(v___x_6008_, 2, v___x_6019_);
                            leanh::lean_ctor_set(v___x_6008_, 1, v___x_6018_);
                            leanh::lean_ctor_set(v___x_6008_, 0, v___x_6017_);
                            v___x_6021_ = v___x_6008_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_6032_ =
                                leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_6032_, 0, v___x_6017_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_6032_, 1, v___x_6018_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_6032_, 2, v___x_6019_);
                            v___x_6021_ = v_reuseFailAlloc_6032_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___x_6011_, 2);
                        leanh::lean_dec(v_tail_6012_);
                        leanh::lean_del_object(v___x_6008_);
                        leanh::lean_dec_ref(v_val_6002_);
                        leanh::lean_dec(v_indName_5994_);
                        v_a_6033_ = leanh::lean_ctor_get(v___x_6013_, 0);
                        v_isSharedCheck_6040_ =
                            (!leanh::lean_is_exclusive(v___x_6013_)) as u8;
                        if v_isSharedCheck_6040_ == 0 {
                            v___x_6035_ = v___x_6013_;
                            v_isShared_6036_ = v_isSharedCheck_6040_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6033_);
                            leanh::lean_dec(v___x_6013_);
                            v___x_6035_ = leanh::lean_box(0);
                            v_isShared_6036_ = v_isSharedCheck_6040_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_6011_);
                    leanh::lean_del_object(v___x_6008_);
                    leanh::lean_dec(v___x_6003_);
                    leanh::lean_dec_ref(v_val_6002_);
                    leanh::lean_dec(v_indName_5994_);
                    v___x_6041_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1_once), _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___closed__1);
                    v___x_6042_ = l_panic___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__7(v___x_6041_, v_a_5995_, v_a_5996_, v_a_5997_, v_a_5998_);
                    return v___x_6042_;
                }
            }
            2 => {
                v___x_6022_ = leanh::lean_box(0);
                v___x_6023_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg(v_val_6002_, v_indName_5994_, v_tail_6012_, v___x_6015_, v___x_6011_, v___x_6016_, v_a_6014_, v___x_6021_, v___x_6022_, v___x_6017_, v_a_5995_, v_a_5996_, v_a_5997_, v_a_5998_);
                leanh::lean_dec_ref(v___x_6021_);
                if leanh::lean_obj_tag(v___x_6023_) == 0 {
                    v_isSharedCheck_6030_ = (!leanh::lean_is_exclusive(v___x_6023_)) as u8;
                    if v_isSharedCheck_6030_ == 0 {
                        v_unused_6031_ = leanh::lean_ctor_get(v___x_6023_, 0);
                        leanh::lean_dec(v_unused_6031_);
                        v___x_6025_ = v___x_6023_;
                        v_isShared_6026_ = v_isSharedCheck_6030_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_6023_);
                        v___x_6025_ = leanh::lean_box(0);
                        v_isShared_6026_ = v_isSharedCheck_6030_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_6023_;
                }
            }
            3 => {
                if v_isShared_6026_ == 0 {
                    leanh::lean_ctor_set(v___x_6025_, 0, v___x_6022_);
                    v___x_6028_ = v___x_6025_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6029_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6029_, 0, v___x_6022_);
                    v___x_6028_ = v_reuseFailAlloc_6029_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6028_;
            }
            5 => {
                if v_isShared_6036_ == 0 {
                    v___x_6038_ = v___x_6035_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6039_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6039_, 0, v_a_6033_);
                    v___x_6038_ = v_reuseFailAlloc_6039_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6038_;
            }
            7 => {
                if v_isShared_6049_ == 0 {
                    v___x_6051_ = v___x_6048_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6052_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6052_, 0, v_a_6046_);
                    v___x_6051_ = v_reuseFailAlloc_6052_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6051_;
            }
            9 => {
                if v_isShared_6059_ == 0 {
                    v___x_6061_ = v___x_6058_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6062_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6062_, 0, v_a_6056_);
                    v___x_6061_ = v_reuseFailAlloc_6062_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6061_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim___boxed(
    mut v_indName_6064_: *mut leanh::LeanObject,
    mut v_a_6065_: *mut leanh::LeanObject,
    mut v_a_6066_: *mut leanh::LeanObject,
    mut v_a_6067_: *mut leanh::LeanObject,
    mut v_a_6068_: *mut leanh::LeanObject,
    mut v_a_6069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6070_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim(
        v_indName_6064_,
        v_a_6065_,
        v_a_6066_,
        v_a_6067_,
        v_a_6068_,
    );
    leanh::lean_dec(v_a_6068_);
    leanh::lean_dec_ref(v_a_6067_);
    leanh::lean_dec(v_a_6066_);
    leanh::lean_dec_ref(v_a_6065_);
    return v_res_6070_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1(
    mut v_val_6071_: *mut leanh::LeanObject,
    mut v_indName_6072_: *mut leanh::LeanObject,
    mut v_tail_6073_: *mut leanh::LeanObject,
    mut v___x_6074_: *mut leanh::LeanObject,
    mut v___x_6075_: *mut leanh::LeanObject,
    mut v___x_6076_: *mut leanh::LeanObject,
    mut v_a_6077_: *mut leanh::LeanObject,
    mut v_range_6078_: *mut leanh::LeanObject,
    mut v_b_6079_: *mut leanh::LeanObject,
    mut v_i_6080_: *mut leanh::LeanObject,
    mut v_hs_6081_: *mut leanh::LeanObject,
    mut v_hl_6082_: *mut leanh::LeanObject,
    mut v___y_6083_: *mut leanh::LeanObject,
    mut v___y_6084_: *mut leanh::LeanObject,
    mut v___y_6085_: *mut leanh::LeanObject,
    mut v___y_6086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6088_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___redArg(v_val_6071_, v_indName_6072_, v_tail_6073_, v___x_6074_, v___x_6075_, v___x_6076_, v_a_6077_, v_range_6078_, v_b_6079_, v_i_6080_, v___y_6083_, v___y_6084_, v___y_6085_, v___y_6086_);
    return v___x_6088_;
}
pub unsafe fn l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_6089_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_indName_6090_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_tail_6091_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___x_6092_: *mut leanh::LeanObject = *_args.add(3);
    let mut v___x_6093_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___x_6094_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_a_6095_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_range_6096_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_b_6097_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_i_6098_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_hs_6099_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_hl_6100_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_6101_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_6102_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_6103_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_6104_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_6105_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_res_6106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6106_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__1(v_val_6089_, v_indName_6090_, v_tail_6091_, v___x_6092_, v___x_6093_, v___x_6094_, v_a_6095_, v_range_6096_, v_b_6097_, v_i_6098_, v_hs_6099_, v_hl_6100_, v___y_6101_, v___y_6102_, v___y_6103_, v___y_6104_);
    leanh::lean_dec(v___y_6104_);
    leanh::lean_dec_ref(v___y_6103_);
    leanh::lean_dec(v___y_6102_);
    leanh::lean_dec_ref(v___y_6101_);
    leanh::lean_dec_ref(v_range_6096_);
    return v_res_6106_;
}
pub unsafe fn l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0(
    mut v_00_u03b1_6107_: *mut leanh::LeanObject,
    mut v_attrName_6108_: *mut leanh::LeanObject,
    mut v_declName_6109_: *mut leanh::LeanObject,
    mut v_asyncPrefix_x3f_6110_: *mut leanh::LeanObject,
    mut v___y_6111_: *mut leanh::LeanObject,
    mut v___y_6112_: *mut leanh::LeanObject,
    mut v___y_6113_: *mut leanh::LeanObject,
    mut v___y_6114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6116_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6116_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___redArg(v_attrName_6108_, v_declName_6109_, v_asyncPrefix_x3f_6110_, v___y_6111_, v___y_6112_, v___y_6113_, v___y_6114_);
    return v___x_6116_;
}
pub unsafe fn l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0___boxed(
    mut v_00_u03b1_6117_: *mut leanh::LeanObject,
    mut v_attrName_6118_: *mut leanh::LeanObject,
    mut v_declName_6119_: *mut leanh::LeanObject,
    mut v_asyncPrefix_x3f_6120_: *mut leanh::LeanObject,
    mut v___y_6121_: *mut leanh::LeanObject,
    mut v___y_6122_: *mut leanh::LeanObject,
    mut v___y_6123_: *mut leanh::LeanObject,
    mut v___y_6124_: *mut leanh::LeanObject,
    mut v___y_6125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6126_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__0(v_00_u03b1_6117_, v_attrName_6118_, v_declName_6119_, v_asyncPrefix_x3f_6120_, v___y_6121_, v___y_6122_, v___y_6123_, v___y_6124_);
    leanh::lean_dec(v___y_6124_);
    leanh::lean_dec_ref(v___y_6123_);
    leanh::lean_dec(v___y_6122_);
    leanh::lean_dec_ref(v___y_6121_);
    return v_res_6126_;
}
pub unsafe fn l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1(
    mut v_00_u03b1_6127_: *mut leanh::LeanObject,
    mut v_attrName_6128_: *mut leanh::LeanObject,
    mut v_declName_6129_: *mut leanh::LeanObject,
    mut v___y_6130_: *mut leanh::LeanObject,
    mut v___y_6131_: *mut leanh::LeanObject,
    mut v___y_6132_: *mut leanh::LeanObject,
    mut v___y_6133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6135_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___redArg(v_attrName_6128_, v_declName_6129_, v___y_6130_, v___y_6131_, v___y_6132_, v___y_6133_);
    return v___x_6135_;
}
pub unsafe fn l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1___boxed(
    mut v_00_u03b1_6136_: *mut leanh::LeanObject,
    mut v_attrName_6137_: *mut leanh::LeanObject,
    mut v_declName_6138_: *mut leanh::LeanObject,
    mut v___y_6139_: *mut leanh::LeanObject,
    mut v___y_6140_: *mut leanh::LeanObject,
    mut v___y_6141_: *mut leanh::LeanObject,
    mut v___y_6142_: *mut leanh::LeanObject,
    mut v___y_6143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6144_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim_spec__0_spec__1(v_00_u03b1_6136_, v_attrName_6137_, v_declName_6138_, v___y_6139_, v___y_6140_, v___y_6141_, v___y_6142_);
    leanh::lean_dec(v___y_6142_);
    leanh::lean_dec_ref(v___y_6141_);
    leanh::lean_dec(v___y_6140_);
    leanh::lean_dec_ref(v___y_6139_);
    return v_res_6144_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0___redArg___lam__0(
    mut v___y_6145_: *mut leanh::LeanObject,
    mut v_isExporting_6146_: u8,
    mut v___x_6147_: *mut leanh::LeanObject,
    mut v___y_6148_: *mut leanh::LeanObject,
    mut v___x_6149_: *mut leanh::LeanObject,
    mut v_a_x3f_6150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6163_: u8 = 0;
    let mut v___x_6164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_6171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6175_: u8 = 0;
    let mut v___x_6177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6182_: u8 = 0;
    let mut v_unused_6183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6185_: u8 = 0;
    let mut v_unused_6186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6152_ = lean_st_ref_take(v___y_6145_);
                v_env_6153_ = leanh::lean_ctor_get(v___x_6152_, 0);
                v_nextMacroScope_6154_ = leanh::lean_ctor_get(v___x_6152_, 1);
                v_ngen_6155_ = leanh::lean_ctor_get(v___x_6152_, 2);
                v_auxDeclNGen_6156_ = leanh::lean_ctor_get(v___x_6152_, 3);
                v_traceState_6157_ = leanh::lean_ctor_get(v___x_6152_, 4);
                v_messages_6158_ = leanh::lean_ctor_get(v___x_6152_, 6);
                v_infoState_6159_ = leanh::lean_ctor_get(v___x_6152_, 7);
                v_snapshotTasks_6160_ = leanh::lean_ctor_get(v___x_6152_, 8);
                v_isSharedCheck_6185_ = (!leanh::lean_is_exclusive(v___x_6152_)) as u8;
                if v_isSharedCheck_6185_ == 0 {
                    v_unused_6186_ = leanh::lean_ctor_get(v___x_6152_, 5);
                    leanh::lean_dec(v_unused_6186_);
                    v___x_6162_ = v___x_6152_;
                    v_isShared_6163_ = v_isSharedCheck_6185_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_6160_);
                    leanh::lean_inc(v_infoState_6159_);
                    leanh::lean_inc(v_messages_6158_);
                    leanh::lean_inc(v_traceState_6157_);
                    leanh::lean_inc(v_auxDeclNGen_6156_);
                    leanh::lean_inc(v_ngen_6155_);
                    leanh::lean_inc(v_nextMacroScope_6154_);
                    leanh::lean_inc(v_env_6153_);
                    leanh::lean_dec(v___x_6152_);
                    v___x_6162_ = leanh::lean_box(0);
                    v_isShared_6163_ = v_isSharedCheck_6185_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6164_ = l_Lean_Environment_setExporting(v_env_6153_, v_isExporting_6146_);
                if v_isShared_6163_ == 0 {
                    leanh::lean_ctor_set(v___x_6162_, 5, v___x_6147_);
                    leanh::lean_ctor_set(v___x_6162_, 0, v___x_6164_);
                    v___x_6166_ = v___x_6162_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6184_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6184_, 0, v___x_6164_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6184_, 1, v_nextMacroScope_6154_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6184_, 2, v_ngen_6155_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6184_, 3, v_auxDeclNGen_6156_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6184_, 4, v_traceState_6157_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6184_, 5, v___x_6147_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6184_, 6, v_messages_6158_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6184_, 7, v_infoState_6159_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6184_, 8, v_snapshotTasks_6160_);
                    v___x_6166_ = v_reuseFailAlloc_6184_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6167_ = lean_st_ref_set(v___y_6145_, v___x_6166_);
                v___x_6168_ = lean_st_ref_take(v___y_6148_);
                v_mctx_6169_ = leanh::lean_ctor_get(v___x_6168_, 0);
                v_zetaDeltaFVarIds_6170_ = leanh::lean_ctor_get(v___x_6168_, 2);
                v_postponed_6171_ = leanh::lean_ctor_get(v___x_6168_, 3);
                v_diag_6172_ = leanh::lean_ctor_get(v___x_6168_, 4);
                v_isSharedCheck_6182_ = (!leanh::lean_is_exclusive(v___x_6168_)) as u8;
                if v_isSharedCheck_6182_ == 0 {
                    v_unused_6183_ = leanh::lean_ctor_get(v___x_6168_, 1);
                    leanh::lean_dec(v_unused_6183_);
                    v___x_6174_ = v___x_6168_;
                    v_isShared_6175_ = v_isSharedCheck_6182_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_6172_);
                    leanh::lean_inc(v_postponed_6171_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_6170_);
                    leanh::lean_inc(v_mctx_6169_);
                    leanh::lean_dec(v___x_6168_);
                    v___x_6174_ = leanh::lean_box(0);
                    v_isShared_6175_ = v_isSharedCheck_6182_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6175_ == 0 {
                    leanh::lean_ctor_set(v___x_6174_, 1, v___x_6149_);
                    v___x_6177_ = v___x_6174_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6181_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6181_, 0, v_mctx_6169_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6181_, 1, v___x_6149_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_6181_,
                        2,
                        v_zetaDeltaFVarIds_6170_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_6181_, 3, v_postponed_6171_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6181_, 4, v_diag_6172_);
                    v___x_6177_ = v_reuseFailAlloc_6181_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6178_ = lean_st_ref_set(v___y_6148_, v___x_6177_);
                v___x_6179_ = leanh::lean_box(0);
                v___x_6180_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6180_, 0, v___x_6179_);
                return v___x_6180_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0___redArg___lam__0___boxed(
    mut v___y_6187_: *mut leanh::LeanObject,
    mut v_isExporting_6188_: *mut leanh::LeanObject,
    mut v___x_6189_: *mut leanh::LeanObject,
    mut v___y_6190_: *mut leanh::LeanObject,
    mut v___x_6191_: *mut leanh::LeanObject,
    mut v_a_x3f_6192_: *mut leanh::LeanObject,
    mut v___y_6193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_6194_: u8 = 0;
    let mut v_res_6195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_6194_ = (leanh::lean_unbox(v_isExporting_6188_) as u8);
    v_res_6195_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0___redArg___lam__0(
        v___y_6187_,
        v_isExporting_boxed_6194_,
        v___x_6189_,
        v___y_6190_,
        v___x_6191_,
        v_a_x3f_6192_,
    );
    leanh::lean_dec(v_a_x3f_6192_);
    leanh::lean_dec(v___y_6190_);
    leanh::lean_dec(v___y_6187_);
    return v_res_6195_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0___redArg(
    mut v_x_6196_: *mut leanh::LeanObject,
    mut v_isExporting_6197_: u8,
    mut v___y_6198_: *mut leanh::LeanObject,
    mut v___y_6199_: *mut leanh::LeanObject,
    mut v___y_6200_: *mut leanh::LeanObject,
    mut v___y_6201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_6205_: u8 = 0;
    let mut v___x_6206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6217_: u8 = 0;
    let mut v___x_6218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_6226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6230_: u8 = 0;
    let mut v___x_6231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_6235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6239_: u8 = 0;
    let mut v___x_6241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6245_: u8 = 0;
    let mut v___x_6247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6249_: u8 = 0;
    let mut v_unused_6250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6252_: u8 = 0;
    let mut v_a_6253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6258_: u8 = 0;
    let mut v___x_6260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6262_: u8 = 0;
    let mut v_unused_6263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6265_: u8 = 0;
    let mut v_unused_6266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6268_: u8 = 0;
    let mut v_unused_6269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6203_ = lean_st_ref_get(v___y_6201_);
                v_env_6204_ = leanh::lean_ctor_get(v___x_6203_, 0);
                leanh::lean_inc_ref(v_env_6204_);
                leanh::lean_dec(v___x_6203_);
                v_isExporting_6205_ = leanh::lean_ctor_get_uint8(
                    v_env_6204_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                leanh::lean_dec_ref(v_env_6204_);
                v___x_6206_ = lean_st_ref_take(v___y_6201_);
                v_env_6207_ = leanh::lean_ctor_get(v___x_6206_, 0);
                v_nextMacroScope_6208_ = leanh::lean_ctor_get(v___x_6206_, 1);
                v_ngen_6209_ = leanh::lean_ctor_get(v___x_6206_, 2);
                v_auxDeclNGen_6210_ = leanh::lean_ctor_get(v___x_6206_, 3);
                v_traceState_6211_ = leanh::lean_ctor_get(v___x_6206_, 4);
                v_messages_6212_ = leanh::lean_ctor_get(v___x_6206_, 6);
                v_infoState_6213_ = leanh::lean_ctor_get(v___x_6206_, 7);
                v_snapshotTasks_6214_ = leanh::lean_ctor_get(v___x_6206_, 8);
                v_isSharedCheck_6268_ = (!leanh::lean_is_exclusive(v___x_6206_)) as u8;
                if v_isSharedCheck_6268_ == 0 {
                    v_unused_6269_ = leanh::lean_ctor_get(v___x_6206_, 5);
                    leanh::lean_dec(v_unused_6269_);
                    v___x_6216_ = v___x_6206_;
                    v_isShared_6217_ = v_isSharedCheck_6268_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_6214_);
                    leanh::lean_inc(v_infoState_6213_);
                    leanh::lean_inc(v_messages_6212_);
                    leanh::lean_inc(v_traceState_6211_);
                    leanh::lean_inc(v_auxDeclNGen_6210_);
                    leanh::lean_inc(v_ngen_6209_);
                    leanh::lean_inc(v_nextMacroScope_6208_);
                    leanh::lean_inc(v_env_6207_);
                    leanh::lean_dec(v___x_6206_);
                    v___x_6216_ = leanh::lean_box(0);
                    v_isShared_6217_ = v_isSharedCheck_6268_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6218_ = l_Lean_Environment_setExporting(v_env_6207_, v_isExporting_6197_);
                v___x_6219_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__2);
                if v_isShared_6217_ == 0 {
                    leanh::lean_ctor_set(v___x_6216_, 5, v___x_6219_);
                    leanh::lean_ctor_set(v___x_6216_, 0, v___x_6218_);
                    v___x_6221_ = v___x_6216_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6267_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6267_, 0, v___x_6218_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6267_, 1, v_nextMacroScope_6208_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6267_, 2, v_ngen_6209_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6267_, 3, v_auxDeclNGen_6210_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6267_, 4, v_traceState_6211_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6267_, 5, v___x_6219_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6267_, 6, v_messages_6212_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6267_, 7, v_infoState_6213_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6267_, 8, v_snapshotTasks_6214_);
                    v___x_6221_ = v_reuseFailAlloc_6267_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6222_ = lean_st_ref_set(v___y_6201_, v___x_6221_);
                v___x_6223_ = lean_st_ref_take(v___y_6199_);
                v_mctx_6224_ = leanh::lean_ctor_get(v___x_6223_, 0);
                v_zetaDeltaFVarIds_6225_ = leanh::lean_ctor_get(v___x_6223_, 2);
                v_postponed_6226_ = leanh::lean_ctor_get(v___x_6223_, 3);
                v_diag_6227_ = leanh::lean_ctor_get(v___x_6223_, 4);
                v_isSharedCheck_6265_ = (!leanh::lean_is_exclusive(v___x_6223_)) as u8;
                if v_isSharedCheck_6265_ == 0 {
                    v_unused_6266_ = leanh::lean_ctor_get(v___x_6223_, 1);
                    leanh::lean_dec(v_unused_6266_);
                    v___x_6229_ = v___x_6223_;
                    v_isShared_6230_ = v_isSharedCheck_6265_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_6227_);
                    leanh::lean_inc(v_postponed_6226_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_6225_);
                    leanh::lean_inc(v_mctx_6224_);
                    leanh::lean_dec(v___x_6223_);
                    v___x_6229_ = leanh::lean_box(0);
                    v_isShared_6230_ = v_isSharedCheck_6265_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6231_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__6_spec__8___redArg___closed__3);
                if v_isShared_6230_ == 0 {
                    leanh::lean_ctor_set(v___x_6229_, 1, v___x_6231_);
                    v___x_6233_ = v___x_6229_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6264_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6264_, 0, v_mctx_6224_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6264_, 1, v___x_6231_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_6264_,
                        2,
                        v_zetaDeltaFVarIds_6225_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_6264_, 3, v_postponed_6226_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6264_, 4, v_diag_6227_);
                    v___x_6233_ = v_reuseFailAlloc_6264_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6234_ = lean_st_ref_set(v___y_6199_, v___x_6233_);
                leanh::lean_inc(v___y_6201_);
                leanh::lean_inc_ref(v___y_6200_);
                leanh::lean_inc(v___y_6199_);
                leanh::lean_inc_ref(v___y_6198_);
                v_r_6235_ = leanh::lean_apply_5(
                    v_x_6196_,
                    v___y_6198_,
                    v___y_6199_,
                    v___y_6200_,
                    v___y_6201_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v_r_6235_) == 0 {
                    v_a_6236_ = leanh::lean_ctor_get(v_r_6235_, 0);
                    v_isSharedCheck_6252_ = (!leanh::lean_is_exclusive(v_r_6235_)) as u8;
                    if v_isSharedCheck_6252_ == 0 {
                        v___x_6238_ = v_r_6235_;
                        v_isShared_6239_ = v_isSharedCheck_6252_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6236_);
                        leanh::lean_dec(v_r_6235_);
                        v___x_6238_ = leanh::lean_box(0);
                        v_isShared_6239_ = v_isSharedCheck_6252_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_6253_ = leanh::lean_ctor_get(v_r_6235_, 0);
                    leanh::lean_inc(v_a_6253_);
                    leanh::lean_dec_ref_known(v_r_6235_, 1);
                    v___x_6254_ = leanh::lean_box(0);
                    v___x_6255_ =
                        l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0___redArg___lam__0(
                            v___y_6201_,
                            v_isExporting_6205_,
                            v___x_6219_,
                            v___y_6199_,
                            v___x_6231_,
                            v___x_6254_,
                        );
                    v_isSharedCheck_6262_ = (!leanh::lean_is_exclusive(v___x_6255_)) as u8;
                    if v_isSharedCheck_6262_ == 0 {
                        v_unused_6263_ = leanh::lean_ctor_get(v___x_6255_, 0);
                        leanh::lean_dec(v_unused_6263_);
                        v___x_6257_ = v___x_6255_;
                        v_isShared_6258_ = v_isSharedCheck_6262_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_6255_);
                        v___x_6257_ = leanh::lean_box(0);
                        v_isShared_6258_ = v_isSharedCheck_6262_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                leanh::lean_inc(v_a_6236_);
                if v_isShared_6239_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6238_, 1);
                    v___x_6241_ = v___x_6238_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6251_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6251_, 0, v_a_6236_);
                    v___x_6241_ = v_reuseFailAlloc_6251_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_6242_ =
                    l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0___redArg___lam__0(
                        v___y_6201_,
                        v_isExporting_6205_,
                        v___x_6219_,
                        v___y_6199_,
                        v___x_6231_,
                        v___x_6241_,
                    );
                leanh::lean_dec_ref(v___x_6241_);
                v_isSharedCheck_6249_ = (!leanh::lean_is_exclusive(v___x_6242_)) as u8;
                if v_isSharedCheck_6249_ == 0 {
                    v_unused_6250_ = leanh::lean_ctor_get(v___x_6242_, 0);
                    leanh::lean_dec(v_unused_6250_);
                    v___x_6244_ = v___x_6242_;
                    v_isShared_6245_ = v_isSharedCheck_6249_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_dec(v___x_6242_);
                    v___x_6244_ = leanh::lean_box(0);
                    v_isShared_6245_ = v_isSharedCheck_6249_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_6245_ == 0 {
                    leanh::lean_ctor_set(v___x_6244_, 0, v_a_6236_);
                    v___x_6247_ = v___x_6244_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6248_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6248_, 0, v_a_6236_);
                    v___x_6247_ = v_reuseFailAlloc_6248_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6247_;
            }
            9 => {
                if v_isShared_6258_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6257_, 1);
                    leanh::lean_ctor_set(v___x_6257_, 0, v_a_6253_);
                    v___x_6260_ = v___x_6257_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6261_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6261_, 0, v_a_6253_);
                    v___x_6260_ = v_reuseFailAlloc_6261_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6260_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0___redArg___boxed(
    mut v_x_6270_: *mut leanh::LeanObject,
    mut v_isExporting_6271_: *mut leanh::LeanObject,
    mut v___y_6272_: *mut leanh::LeanObject,
    mut v___y_6273_: *mut leanh::LeanObject,
    mut v___y_6274_: *mut leanh::LeanObject,
    mut v___y_6275_: *mut leanh::LeanObject,
    mut v___y_6276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_6277_: u8 = 0;
    let mut v_res_6278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_6277_ = (leanh::lean_unbox(v_isExporting_6271_) as u8);
    v_res_6278_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0___redArg(
        v_x_6270_,
        v_isExporting_boxed_6277_,
        v___y_6272_,
        v___y_6273_,
        v___y_6274_,
        v___y_6275_,
    );
    leanh::lean_dec(v___y_6275_);
    leanh::lean_dec_ref(v___y_6274_);
    leanh::lean_dec(v___y_6273_);
    leanh::lean_dec_ref(v___y_6272_);
    return v_res_6278_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0(
    mut v_00_u03b1_6279_: *mut leanh::LeanObject,
    mut v_x_6280_: *mut leanh::LeanObject,
    mut v_isExporting_6281_: u8,
    mut v___y_6282_: *mut leanh::LeanObject,
    mut v___y_6283_: *mut leanh::LeanObject,
    mut v___y_6284_: *mut leanh::LeanObject,
    mut v___y_6285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6287_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0___redArg(
        v_x_6280_,
        v_isExporting_6281_,
        v___y_6282_,
        v___y_6283_,
        v___y_6284_,
        v___y_6285_,
    );
    return v___x_6287_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0___boxed(
    mut v_00_u03b1_6288_: *mut leanh::LeanObject,
    mut v_x_6289_: *mut leanh::LeanObject,
    mut v_isExporting_6290_: *mut leanh::LeanObject,
    mut v___y_6291_: *mut leanh::LeanObject,
    mut v___y_6292_: *mut leanh::LeanObject,
    mut v___y_6293_: *mut leanh::LeanObject,
    mut v___y_6294_: *mut leanh::LeanObject,
    mut v___y_6295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_6296_: u8 = 0;
    let mut v_res_6297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_6296_ = (leanh::lean_unbox(v_isExporting_6290_) as u8);
    v_res_6297_ = l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0(
        v_00_u03b1_6288_,
        v_x_6289_,
        v_isExporting_boxed_6296_,
        v___y_6291_,
        v___y_6292_,
        v___y_6293_,
        v___y_6294_,
    );
    leanh::lean_dec(v___y_6294_);
    leanh::lean_dec_ref(v___y_6293_);
    leanh::lean_dec(v___y_6292_);
    leanh::lean_dec_ref(v___y_6291_);
    return v_res_6297_;
}
pub unsafe fn l_Lean_mkCtorElim___lam__0(
    mut v_indName_6298_: *mut leanh::LeanObject,
    mut v___y_6299_: *mut leanh::LeanObject,
    mut v___y_6300_: *mut leanh::LeanObject,
    mut v___y_6301_: *mut leanh::LeanObject,
    mut v___y_6302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6304_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_indName_6298_);
    v___x_6304_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType(
        v_indName_6298_,
        v___y_6299_,
        v___y_6300_,
        v___y_6301_,
        v___y_6302_,
    );
    if leanh::lean_obj_tag(v___x_6304_) == 0 {
        let mut v___x_6305_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_6304_, 1);
        leanh::lean_inc(v_indName_6298_);
        v___x_6305_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkIndCtorElim(
            v_indName_6298_,
            v___y_6299_,
            v___y_6300_,
            v___y_6301_,
            v___y_6302_,
        );
        if leanh::lean_obj_tag(v___x_6305_) == 0 {
            let mut v___x_6306_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v___x_6305_, 1);
            v___x_6306_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_mkConstructorElim(
                v_indName_6298_,
                v___y_6299_,
                v___y_6300_,
                v___y_6301_,
                v___y_6302_,
            );
            return v___x_6306_;
        } else {
            leanh::lean_dec(v_indName_6298_);
            return v___x_6305_;
        }
    } else {
        leanh::lean_dec(v_indName_6298_);
        return v___x_6304_;
    }
}
pub unsafe fn l_Lean_mkCtorElim___lam__0___boxed(
    mut v_indName_6307_: *mut leanh::LeanObject,
    mut v___y_6308_: *mut leanh::LeanObject,
    mut v___y_6309_: *mut leanh::LeanObject,
    mut v___y_6310_: *mut leanh::LeanObject,
    mut v___y_6311_: *mut leanh::LeanObject,
    mut v___y_6312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6313_ = l_Lean_mkCtorElim___lam__0(
        v_indName_6307_,
        v___y_6308_,
        v___y_6309_,
        v___y_6310_,
        v___y_6311_,
    );
    leanh::lean_dec(v___y_6311_);
    leanh::lean_dec_ref(v___y_6310_);
    leanh::lean_dec(v___y_6309_);
    leanh::lean_dec_ref(v___y_6308_);
    return v_res_6313_;
}
pub unsafe fn l_Lean_mkCtorElim(
    mut v_indName_6314_: *mut leanh::LeanObject,
    mut v_a_6315_: *mut leanh::LeanObject,
    mut v_a_6316_: *mut leanh::LeanObject,
    mut v_a_6317_: *mut leanh::LeanObject,
    mut v_a_6318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6323_: u8 = 0;
    let mut v___x_6324_: u8 = 0;
    let mut v___x_6325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6331_: u8 = 0;
    let mut v_val_6332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: u8 = 0;
    let mut v___x_6336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_6340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_6341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6347_: u8 = 0;
    let mut v___x_6348_: u8 = 0;
    let mut v___x_6349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6354_: u8 = 0;
    let mut v___x_6355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: u8 = 0;
    let mut v___x_6359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: u8 = 0;
    let mut v___x_6365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6366_: u8 = 0;
    let mut v___x_6367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6368_: u8 = 0;
    let mut v_a_6369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6372_: u8 = 0;
    let mut v___x_6374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6376_: u8 = 0;
    let mut v___x_6377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6381_: u8 = 0;
    let mut v_a_6382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6385_: u8 = 0;
    let mut v___x_6387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6389_: u8 = 0;
    let mut v___x_6390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6394_: u8 = 0;
    let mut v_a_6395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6398_: u8 = 0;
    let mut v___x_6400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6402_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6320_ = lean_st_ref_get(v_a_6318_);
                v_env_6321_ = leanh::lean_ctor_get(v___x_6320_, 0);
                leanh::lean_inc_ref(v_env_6321_);
                leanh::lean_dec(v___x_6320_);
                leanh::lean_inc(v_indName_6314_);
                v___x_6322_ = l_mkCtorIdxName(v_indName_6314_);
                v___x_6323_ = 1;
                v___x_6324_ = l_Lean_Environment_contains(v_env_6321_, v___x_6322_, v___x_6323_);
                if v___x_6324_ == 0 {
                    leanh::lean_dec(v_indName_6314_);
                    v___x_6325_ = leanh::lean_box(0);
                    v___x_6326_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6326_, 0, v___x_6325_);
                    return v___x_6326_;
                } else {
                    leanh::lean_inc(v_indName_6314_);
                    v___x_6327_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v_indName_6314_, v_a_6315_, v_a_6316_, v_a_6317_, v_a_6318_);
                    if leanh::lean_obj_tag(v___x_6327_) == 0 {
                        v_a_6328_ = leanh::lean_ctor_get(v___x_6327_, 0);
                        v_isSharedCheck_6394_ =
                            (!leanh::lean_is_exclusive(v___x_6327_)) as u8;
                        if v_isSharedCheck_6394_ == 0 {
                            v___x_6330_ = v___x_6327_;
                            v_isShared_6331_ = v_isSharedCheck_6394_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6328_);
                            leanh::lean_dec(v___x_6327_);
                            v___x_6330_ = leanh::lean_box(0);
                            v_isShared_6331_ = v_isSharedCheck_6394_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_indName_6314_);
                        v_a_6395_ = leanh::lean_ctor_get(v___x_6327_, 0);
                        v_isSharedCheck_6402_ =
                            (!leanh::lean_is_exclusive(v___x_6327_)) as u8;
                        if v_isSharedCheck_6402_ == 0 {
                            v___x_6397_ = v___x_6327_;
                            v_isShared_6398_ = v_isSharedCheck_6402_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6395_);
                            leanh::lean_dec(v___x_6327_);
                            v___x_6397_ = leanh::lean_box(0);
                            v_isShared_6398_ = v_isSharedCheck_6402_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_6328_) == 5 {
                    v_val_6332_ = leanh::lean_ctor_get(v_a_6328_, 0);
                    leanh::lean_inc_ref(v_val_6332_);
                    leanh::lean_dec_ref_known(v_a_6328_, 1);
                    v___x_6333_ = leanh::lean_unsigned_to_nat(1);
                    v___x_6334_ = l_Lean_InductiveVal_numCtors(v_val_6332_);
                    v___x_6335_ = lean_nat_dec_lt(v___x_6333_, v___x_6334_);
                    leanh::lean_dec(v___x_6334_);
                    if v___x_6335_ == 0 {
                        leanh::lean_dec_ref(v_val_6332_);
                        leanh::lean_dec(v_indName_6314_);
                        v___x_6336_ = leanh::lean_box(0);
                        if v_isShared_6331_ == 0 {
                            leanh::lean_ctor_set(v___x_6330_, 0, v___x_6336_);
                            v___x_6338_ = v___x_6330_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_6339_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_6339_, 0, v___x_6336_);
                            v___x_6338_ = v_reuseFailAlloc_6339_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_6330_);
                        v_toConstantVal_6340_ = leanh::lean_ctor_get(v_val_6332_, 0);
                        leanh::lean_inc_ref(v_toConstantVal_6340_);
                        leanh::lean_dec_ref(v_val_6332_);
                        v_levelParams_6341_ = leanh::lean_ctor_get(v_toConstantVal_6340_, 1);
                        leanh::lean_inc(v_levelParams_6341_);
                        v_type_6342_ = leanh::lean_ctor_get(v_toConstantVal_6340_, 2);
                        leanh::lean_inc_ref(v_type_6342_);
                        leanh::lean_dec_ref(v_toConstantVal_6340_);
                        v___x_6343_ = l_Lean_Meta_isPropFormerType(
                            v_type_6342_,
                            v_a_6315_,
                            v_a_6316_,
                            v_a_6317_,
                            v_a_6318_,
                        );
                        if leanh::lean_obj_tag(v___x_6343_) == 0 {
                            v_a_6344_ = leanh::lean_ctor_get(v___x_6343_, 0);
                            v_isSharedCheck_6381_ =
                                (!leanh::lean_is_exclusive(v___x_6343_)) as u8;
                            if v_isSharedCheck_6381_ == 0 {
                                v___x_6346_ = v___x_6343_;
                                v_isShared_6347_ = v_isSharedCheck_6381_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6344_);
                                leanh::lean_dec(v___x_6343_);
                                v___x_6346_ = leanh::lean_box(0);
                                v_isShared_6347_ = v_isSharedCheck_6381_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_levelParams_6341_);
                            leanh::lean_dec(v_indName_6314_);
                            v_a_6382_ = leanh::lean_ctor_get(v___x_6343_, 0);
                            v_isSharedCheck_6389_ =
                                (!leanh::lean_is_exclusive(v___x_6343_)) as u8;
                            if v_isSharedCheck_6389_ == 0 {
                                v___x_6384_ = v___x_6343_;
                                v_isShared_6385_ = v_isSharedCheck_6389_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6382_);
                                leanh::lean_dec(v___x_6343_);
                                v___x_6384_ = leanh::lean_box(0);
                                v_isShared_6385_ = v_isSharedCheck_6389_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_6328_);
                    leanh::lean_dec(v_indName_6314_);
                    v___x_6390_ = leanh::lean_box(0);
                    if v_isShared_6331_ == 0 {
                        leanh::lean_ctor_set(v___x_6330_, 0, v___x_6390_);
                        v___x_6392_ = v___x_6330_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_6393_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6393_, 0, v___x_6390_);
                        v___x_6392_ = v_reuseFailAlloc_6393_;
                        state = 11;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6338_;
            }
            3 => {
                v___x_6348_ = (leanh::lean_unbox(v_a_6344_) as u8);
                if v___x_6348_ == 0 {
                    leanh::lean_del_object(v___x_6346_);
                    leanh::lean_inc(v_indName_6314_);
                    v___x_6349_ = l_Lean_mkRecName(v_indName_6314_);
                    v___x_6350_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0(v___x_6349_, v_a_6315_, v_a_6316_, v_a_6317_, v_a_6318_);
                    if leanh::lean_obj_tag(v___x_6350_) == 0 {
                        v_a_6351_ = leanh::lean_ctor_get(v___x_6350_, 0);
                        v_isSharedCheck_6368_ =
                            (!leanh::lean_is_exclusive(v___x_6350_)) as u8;
                        if v_isSharedCheck_6368_ == 0 {
                            v___x_6353_ = v___x_6350_;
                            v_isShared_6354_ = v_isSharedCheck_6368_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6351_);
                            leanh::lean_dec(v___x_6350_);
                            v___x_6353_ = leanh::lean_box(0);
                            v_isShared_6354_ = v_isSharedCheck_6368_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_6344_);
                        leanh::lean_dec(v_levelParams_6341_);
                        leanh::lean_dec(v_indName_6314_);
                        v_a_6369_ = leanh::lean_ctor_get(v___x_6350_, 0);
                        v_isSharedCheck_6376_ =
                            (!leanh::lean_is_exclusive(v___x_6350_)) as u8;
                        if v_isSharedCheck_6376_ == 0 {
                            v___x_6371_ = v___x_6350_;
                            v_isShared_6372_ = v_isSharedCheck_6376_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6369_);
                            leanh::lean_dec(v___x_6350_);
                            v___x_6371_ = leanh::lean_box(0);
                            v_isShared_6372_ = v_isSharedCheck_6376_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_6344_);
                    leanh::lean_dec(v_levelParams_6341_);
                    leanh::lean_dec(v_indName_6314_);
                    v___x_6377_ = leanh::lean_box(0);
                    if v_isShared_6347_ == 0 {
                        leanh::lean_ctor_set(v___x_6346_, 0, v___x_6377_);
                        v___x_6379_ = v___x_6346_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6380_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6380_, 0, v___x_6377_);
                        v___x_6379_ = v_reuseFailAlloc_6380_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                v___x_6355_ = l_List_lengthTR___redArg(v_levelParams_6341_);
                leanh::lean_dec(v_levelParams_6341_);
                v___x_6356_ = l_Lean_ConstantInfo_levelParams(v_a_6351_);
                leanh::lean_dec(v_a_6351_);
                v___x_6357_ = l_List_lengthTR___redArg(v___x_6356_);
                leanh::lean_dec(v___x_6356_);
                v___x_6358_ = lean_nat_dec_lt(v___x_6355_, v___x_6357_);
                leanh::lean_dec(v___x_6357_);
                leanh::lean_dec(v___x_6355_);
                if v___x_6358_ == 0 {
                    leanh::lean_dec(v_a_6344_);
                    leanh::lean_dec(v_indName_6314_);
                    v___x_6359_ = leanh::lean_box(0);
                    if v_isShared_6354_ == 0 {
                        leanh::lean_ctor_set(v___x_6353_, 0, v___x_6359_);
                        v___x_6361_ = v___x_6353_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6362_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6362_, 0, v___x_6359_);
                        v___x_6361_ = v_reuseFailAlloc_6362_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6353_);
                    leanh::lean_inc(v_indName_6314_);
                    v___f_6363_ = leanh::lean_alloc_closure(
                        l_Lean_mkCtorElim___lam__0___boxed as *mut core::ffi::c_void,
                        6,
                        1,
                    );
                    leanh::lean_closure_set(v___f_6363_, 0, v_indName_6314_);
                    v___x_6364_ = l_Lean_isPrivateName(v_indName_6314_);
                    leanh::lean_dec(v_indName_6314_);
                    if v___x_6364_ == 0 {
                        leanh::lean_dec(v_a_6344_);
                        v___x_6365_ =
                            l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0___redArg(
                                v___f_6363_,
                                v___x_6324_,
                                v_a_6315_,
                                v_a_6316_,
                                v_a_6317_,
                                v_a_6318_,
                            );
                        return v___x_6365_;
                    } else {
                        v___x_6366_ = (leanh::lean_unbox(v_a_6344_) as u8);
                        leanh::lean_dec(v_a_6344_);
                        v___x_6367_ =
                            l_Lean_withExporting___at___00Lean_mkCtorElim_spec__0___redArg(
                                v___f_6363_,
                                v___x_6366_,
                                v_a_6315_,
                                v_a_6316_,
                                v_a_6317_,
                                v_a_6318_,
                            );
                        return v___x_6367_;
                    }
                }
            }
            5 => {
                return v___x_6361_;
            }
            6 => {
                if v_isShared_6372_ == 0 {
                    v___x_6374_ = v___x_6371_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6375_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6375_, 0, v_a_6369_);
                    v___x_6374_ = v_reuseFailAlloc_6375_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6374_;
            }
            8 => {
                return v___x_6379_;
            }
            9 => {
                if v_isShared_6385_ == 0 {
                    v___x_6387_ = v___x_6384_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6388_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6388_, 0, v_a_6382_);
                    v___x_6387_ = v_reuseFailAlloc_6388_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6387_;
            }
            11 => {
                return v___x_6392_;
            }
            12 => {
                if v_isShared_6398_ == 0 {
                    v___x_6400_ = v___x_6397_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6401_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6401_, 0, v_a_6395_);
                    v___x_6400_ = v_reuseFailAlloc_6401_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6400_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkCtorElim___boxed(
    mut v_indName_6403_: *mut leanh::LeanObject,
    mut v_a_6404_: *mut leanh::LeanObject,
    mut v_a_6405_: *mut leanh::LeanObject,
    mut v_a_6406_: *mut leanh::LeanObject,
    mut v_a_6407_: *mut leanh::LeanObject,
    mut v_a_6408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6409_ = l_Lean_mkCtorElim(v_indName_6403_, v_a_6404_, v_a_6405_, v_a_6406_, v_a_6407_);
    leanh::lean_dec(v_a_6407_);
    leanh::lean_dec_ref(v_a_6406_);
    leanh::lean_dec(v_a_6405_);
    leanh::lean_dec_ref(v_a_6404_);
    return v_res_6409_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(
    mut v_decl_6410_: *mut leanh::LeanObject,
    mut v_____r_6411_: *mut leanh::LeanObject,
    mut v___y_6412_: *mut leanh::LeanObject,
    mut v___y_6413_: *mut leanh::LeanObject,
    mut v___y_6414_: *mut leanh::LeanObject,
    mut v___y_6415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6417_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_decl_6410_);
    v___x_6417_ = l_mkCtorIdx(
        v_decl_6410_,
        v___y_6412_,
        v___y_6413_,
        v___y_6414_,
        v___y_6415_,
    );
    if leanh::lean_obj_tag(v___x_6417_) == 0 {
        let mut v___x_6418_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_6417_, 1);
        v___x_6418_ = l_Lean_mkCtorElim(
            v_decl_6410_,
            v___y_6412_,
            v___y_6413_,
            v___y_6414_,
            v___y_6415_,
        );
        return v___x_6418_;
    } else {
        leanh::lean_dec(v_decl_6410_);
        return v___x_6417_;
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(
    mut v_decl_6419_: *mut leanh::LeanObject,
    mut v_____r_6420_: *mut leanh::LeanObject,
    mut v___y_6421_: *mut leanh::LeanObject,
    mut v___y_6422_: *mut leanh::LeanObject,
    mut v___y_6423_: *mut leanh::LeanObject,
    mut v___y_6424_: *mut leanh::LeanObject,
    mut v___y_6425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6426_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v_decl_6419_, v_____r_6420_, v___y_6421_, v___y_6422_, v___y_6423_, v___y_6424_);
    leanh::lean_dec(v___y_6424_);
    leanh::lean_dec_ref(v___y_6423_);
    leanh::lean_dec(v___y_6422_);
    leanh::lean_dec_ref(v___y_6421_);
    return v_res_6426_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6428_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__0;
    v___x_6429_ = l_Lean_stringToMessageData(v___x_6428_);
    return v___x_6429_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_6431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6431_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__2;
    v___x_6432_ = l_Lean_stringToMessageData(v___x_6431_);
    return v___x_6432_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg(
    mut v_name_6436_: *mut leanh::LeanObject,
    mut v_kind_6437_: u8,
    mut v___y_6438_: *mut leanh::LeanObject,
    mut v___y_6439_: *mut leanh::LeanObject,
    mut v___y_6440_: *mut leanh::LeanObject,
    mut v___y_6441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6443_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__1);
                v___x_6444_ = l_Lean_MessageData_ofName(v_name_6436_);
                v___x_6445_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6445_, 0, v___x_6443_);
                leanh::lean_ctor_set(v___x_6445_, 1, v___x_6444_);
                v___x_6446_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__3);
                v___x_6447_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6447_, 0, v___x_6445_);
                leanh::lean_ctor_set(v___x_6447_, 1, v___x_6446_);
                match v_kind_6437_ {
                    0 => {
                        v___x_6456_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__4;
                        v___y_6449_ = v___x_6456_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v___x_6457_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__5;
                        v___y_6449_ = v___x_6457_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_6458_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___closed__6;
                        v___y_6449_ = v___x_6458_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v___y_6449_);
                v___x_6450_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6450_, 0, v___y_6449_);
                v___x_6451_ = l_Lean_MessageData_ofFormat(v___x_6450_);
                v___x_6452_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6452_, 0, v___x_6447_);
                leanh::lean_ctor_set(v___x_6452_, 1, v___x_6451_);
                v___x_6453_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4___redArg___closed__3);
                v___x_6454_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6454_, 0, v___x_6452_);
                leanh::lean_ctor_set(v___x_6454_, 1, v___x_6453_);
                v___x_6455_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_withMkPULiftUp_spec__0___redArg(v___x_6454_, v___y_6438_, v___y_6439_, v___y_6440_, v___y_6441_);
                return v___x_6455_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg___boxed(
    mut v_name_6459_: *mut leanh::LeanObject,
    mut v_kind_6460_: *mut leanh::LeanObject,
    mut v___y_6461_: *mut leanh::LeanObject,
    mut v___y_6462_: *mut leanh::LeanObject,
    mut v___y_6463_: *mut leanh::LeanObject,
    mut v___y_6464_: *mut leanh::LeanObject,
    mut v___y_6465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_6466_: u8 = 0;
    let mut v_res_6467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_6466_ = (leanh::lean_unbox(v_kind_6460_) as u8);
    v_res_6467_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg(v_name_6459_, v_kind_boxed_6466_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_);
    leanh::lean_dec(v___y_6464_);
    leanh::lean_dec_ref(v___y_6463_);
    leanh::lean_dec(v___y_6462_);
    leanh::lean_dec_ref(v___y_6461_);
    return v_res_6467_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_()
-> u64 {
    let mut v___x_6474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6475_: u64 = 0;
    v___x_6474_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_;
    v___x_6475_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_6474_);
    return v___x_6475_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_6476_: u64 = 0;
    let mut v___x_6477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6476_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
    v___x_6477_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_;
    v___x_6478_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
    leanh::lean_ctor_set(v___x_6478_, 0, v___x_6477_);
    leanh::lean_ctor_set_uint64(
        v___x_6478_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_6476_,
    );
    return v___x_6478_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_6479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6479_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_6479_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_6480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6480_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
    v___x_6481_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6481_, 0, v___x_6480_);
    return v___x_6481_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_6482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6482_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
    v___x_6483_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_6483_, 0, v___x_6482_);
    leanh::lean_ctor_set(v___x_6483_, 1, v___x_6482_);
    leanh::lean_ctor_set(v___x_6483_, 2, v___x_6482_);
    leanh::lean_ctor_set(v___x_6483_, 3, v___x_6482_);
    leanh::lean_ctor_set(v___x_6483_, 4, v___x_6482_);
    leanh::lean_ctor_set(v___x_6483_, 5, v___x_6482_);
    return v___x_6483_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__6_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_6484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6484_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
    v___x_6485_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_6485_, 0, v___x_6484_);
    leanh::lean_ctor_set(v___x_6485_, 1, v___x_6484_);
    leanh::lean_ctor_set(v___x_6485_, 2, v___x_6484_);
    leanh::lean_ctor_set(v___x_6485_, 3, v___x_6484_);
    leanh::lean_ctor_set(v___x_6485_, 4, v___x_6484_);
    return v___x_6485_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(
    mut v___x_6486_: *mut leanh::LeanObject,
    mut v___x_6487_: *mut leanh::LeanObject,
    mut v___x_6488_: *mut leanh::LeanObject,
    mut v_decl_6489_: *mut leanh::LeanObject,
    mut v___stx_6490_: *mut leanh::LeanObject,
    mut v_kind_6491_: u8,
    mut v___y_6492_: *mut leanh::LeanObject,
    mut v___y_6493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6495_: u8 = 0;
    let mut v___x_6496_: u8 = 0;
    let mut v___x_6497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: usize = 0;
    let mut v___x_6503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6519_: u8 = 0;
    let mut v___x_6520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6524_: u8 = 0;
    let mut v___x_6525_: u8 = 0;
    let mut v___x_6526_: u8 = 0;
    let mut v___x_6527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6495_ = 1;
                v___x_6496_ = 0;
                v___x_6497_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
                v___x_6498_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
                v___x_6499_ = leanh::lean_unsigned_to_nat(32);
                v___x_6500_ = lean_mk_empty_array_with_capacity(v___x_6499_);
                v___x_6501_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__3);
                v___x_6502_ = 5usize;
                leanh::lean_inc_n(v___x_6486_, 6);
                v___x_6503_ =
                    leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                leanh::lean_ctor_set(v___x_6503_, 0, v___x_6501_);
                leanh::lean_ctor_set(v___x_6503_, 1, v___x_6500_);
                leanh::lean_ctor_set(v___x_6503_, 2, v___x_6486_);
                leanh::lean_ctor_set(v___x_6503_, 3, v___x_6486_);
                leanh::lean_ctor_set_usize(v___x_6503_, 4, v___x_6502_);
                v___x_6504_ = leanh::lean_box(1);
                leanh::lean_inc_ref(v___x_6503_);
                v___x_6505_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_6505_, 0, v___x_6498_);
                leanh::lean_ctor_set(v___x_6505_, 1, v___x_6503_);
                leanh::lean_ctor_set(v___x_6505_, 2, v___x_6504_);
                v___x_6506_ = lean_mk_empty_array_with_capacity(v___x_6486_);
                v___x_6507_ = leanh::lean_box(0);
                leanh::lean_inc(v___x_6487_);
                v___x_6508_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_6508_, 0, v___x_6497_);
                leanh::lean_ctor_set(v___x_6508_, 1, v___x_6487_);
                leanh::lean_ctor_set(v___x_6508_, 2, v___x_6505_);
                leanh::lean_ctor_set(v___x_6508_, 3, v___x_6506_);
                leanh::lean_ctor_set(v___x_6508_, 4, v___x_6507_);
                leanh::lean_ctor_set(v___x_6508_, 5, v___x_6486_);
                leanh::lean_ctor_set(v___x_6508_, 6, v___x_6507_);
                leanh::lean_ctor_set_uint8(
                    v___x_6508_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v___x_6496_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6508_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v___x_6496_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6508_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v___x_6496_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6508_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v___x_6495_,
                );
                v___x_6509_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                leanh::lean_ctor_set(v___x_6509_, 0, v___x_6486_);
                leanh::lean_ctor_set(v___x_6509_, 1, v___x_6486_);
                leanh::lean_ctor_set(v___x_6509_, 2, v___x_6486_);
                leanh::lean_ctor_set(v___x_6509_, 3, v___x_6486_);
                leanh::lean_ctor_set(v___x_6509_, 4, v___x_6498_);
                leanh::lean_ctor_set(v___x_6509_, 5, v___x_6498_);
                leanh::lean_ctor_set(v___x_6509_, 6, v___x_6498_);
                leanh::lean_ctor_set(v___x_6509_, 7, v___x_6498_);
                leanh::lean_ctor_set(v___x_6509_, 8, v___x_6498_);
                leanh::lean_ctor_set(v___x_6509_, 9, v___x_6498_);
                v___x_6510_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
                v___x_6511_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__6_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__6_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1___closed__6_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
                v___x_6512_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_6512_, 0, v___x_6509_);
                leanh::lean_ctor_set(v___x_6512_, 1, v___x_6510_);
                leanh::lean_ctor_set(v___x_6512_, 2, v___x_6487_);
                leanh::lean_ctor_set(v___x_6512_, 3, v___x_6503_);
                leanh::lean_ctor_set(v___x_6512_, 4, v___x_6511_);
                v___x_6513_ = lean_st_mk_ref(v___x_6512_);
                v___x_6525_ = 0;
                v___x_6526_ = l_Lean_instBEqAttributeKind_beq(v_kind_6491_, v___x_6525_);
                if v___x_6526_ == 0 {
                    leanh::lean_dec(v_decl_6489_);
                    v___x_6527_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg(v___x_6488_, v_kind_6491_, v___x_6508_, v___x_6513_, v___y_6492_, v___y_6493_);
                    leanh::lean_dec_ref_known(v___x_6508_, 7);
                    v___y_6515_ = v___x_6527_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_6488_);
                    v___x_6528_ = leanh::lean_box(0);
                    v___x_6529_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v_decl_6489_, v___x_6528_, v___x_6508_, v___x_6513_, v___y_6492_, v___y_6493_);
                    leanh::lean_dec_ref_known(v___x_6508_, 7);
                    v___y_6515_ = v___x_6529_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_6515_) == 0 {
                    v_a_6516_ = leanh::lean_ctor_get(v___y_6515_, 0);
                    v_isSharedCheck_6524_ = (!leanh::lean_is_exclusive(v___y_6515_)) as u8;
                    if v_isSharedCheck_6524_ == 0 {
                        v___x_6518_ = v___y_6515_;
                        v_isShared_6519_ = v_isSharedCheck_6524_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6516_);
                        leanh::lean_dec(v___y_6515_);
                        v___x_6518_ = leanh::lean_box(0);
                        v_isShared_6519_ = v_isSharedCheck_6524_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_6513_);
                    return v___y_6515_;
                }
            }
            2 => {
                v___x_6520_ = lean_st_ref_get(v___x_6513_);
                leanh::lean_dec(v___x_6513_);
                leanh::lean_dec(v___x_6520_);
                if v_isShared_6519_ == 0 {
                    v___x_6522_ = v___x_6518_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6523_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6523_, 0, v_a_6516_);
                    v___x_6522_ = v_reuseFailAlloc_6523_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6522_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(
    mut v___x_6530_: *mut leanh::LeanObject,
    mut v___x_6531_: *mut leanh::LeanObject,
    mut v___x_6532_: *mut leanh::LeanObject,
    mut v_decl_6533_: *mut leanh::LeanObject,
    mut v___stx_6534_: *mut leanh::LeanObject,
    mut v_kind_6535_: *mut leanh::LeanObject,
    mut v___y_6536_: *mut leanh::LeanObject,
    mut v___y_6537_: *mut leanh::LeanObject,
    mut v___y_6538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_6539_: u8 = 0;
    let mut v_res_6540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_6539_ = (leanh::lean_unbox(v_kind_6535_) as u8);
    v_res_6540_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v___x_6530_, v___x_6531_, v___x_6532_, v_decl_6533_, v___stx_6534_, v_kind_boxed_6539_, v___y_6536_, v___y_6537_);
    leanh::lean_dec(v___y_6537_);
    leanh::lean_dec_ref(v___y_6536_);
    leanh::lean_dec(v___stx_6534_);
    return v_res_6540_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0(
    mut v_msgData_6541_: *mut leanh::LeanObject,
    mut v___y_6542_: *mut leanh::LeanObject,
    mut v___y_6543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6545_ = lean_st_ref_get(v___y_6543_);
    v_env_6546_ = leanh::lean_ctor_get(v___x_6545_, 0);
    leanh::lean_inc_ref(v_env_6546_);
    leanh::lean_dec(v___x_6545_);
    v_options_6547_ = leanh::lean_ctor_get(v___y_6542_, 2);
    v___x_6548_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__2);
    v___x_6549_ = leanh::lean_unsigned_to_nat(32);
    v___x_6550_ = lean_mk_empty_array_with_capacity(v___x_6549_);
    leanh::lean_dec_ref(v___x_6550_);
    v___x_6551_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_mkCtorElimType_spec__0_spec__0_spec__4_spec__11_spec__12_spec__13___redArg___closed__5);
    leanh::lean_inc_ref(v_options_6547_);
    v___x_6552_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_6552_, 0, v_env_6546_);
    leanh::lean_ctor_set(v___x_6552_, 1, v___x_6548_);
    leanh::lean_ctor_set(v___x_6552_, 2, v___x_6551_);
    leanh::lean_ctor_set(v___x_6552_, 3, v_options_6547_);
    v___x_6553_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6553_, 0, v___x_6552_);
    leanh::lean_ctor_set(v___x_6553_, 1, v_msgData_6541_);
    v___x_6554_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6554_, 0, v___x_6553_);
    return v___x_6554_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_msgData_6555_: *mut leanh::LeanObject,
    mut v___y_6556_: *mut leanh::LeanObject,
    mut v___y_6557_: *mut leanh::LeanObject,
    mut v___y_6558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6559_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0(v_msgData_6555_, v___y_6556_, v___y_6557_);
    leanh::lean_dec(v___y_6557_);
    leanh::lean_dec_ref(v___y_6556_);
    return v_res_6559_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg(
    mut v_msg_6560_: *mut leanh::LeanObject,
    mut v___y_6561_: *mut leanh::LeanObject,
    mut v___y_6562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_6564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6569_: u8 = 0;
    let mut v___x_6570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6574_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_6564_ = leanh::lean_ctor_get(v___y_6561_, 5);
                v___x_6565_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0_spec__0(v_msg_6560_, v___y_6561_, v___y_6562_);
                v_a_6566_ = leanh::lean_ctor_get(v___x_6565_, 0);
                v_isSharedCheck_6574_ = (!leanh::lean_is_exclusive(v___x_6565_)) as u8;
                if v_isSharedCheck_6574_ == 0 {
                    v___x_6568_ = v___x_6565_;
                    v_isShared_6569_ = v_isSharedCheck_6574_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_6566_);
                    leanh::lean_dec(v___x_6565_);
                    v___x_6568_ = leanh::lean_box(0);
                    v_isShared_6569_ = v_isSharedCheck_6574_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_6564_);
                v___x_6570_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6570_, 0, v_ref_6564_);
                leanh::lean_ctor_set(v___x_6570_, 1, v_a_6566_);
                if v_isShared_6569_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6568_, 1);
                    leanh::lean_ctor_set(v___x_6568_, 0, v___x_6570_);
                    v___x_6572_ = v___x_6568_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6573_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6573_, 0, v___x_6570_);
                    v___x_6572_ = v_reuseFailAlloc_6573_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6572_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_msg_6575_: *mut leanh::LeanObject,
    mut v___y_6576_: *mut leanh::LeanObject,
    mut v___y_6577_: *mut leanh::LeanObject,
    mut v___y_6578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6579_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg(v_msg_6575_, v___y_6576_, v___y_6577_);
    leanh::lean_dec(v___y_6577_);
    leanh::lean_dec_ref(v___y_6576_);
    return v_res_6579_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_6581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6581_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_;
    v___x_6582_ = l_Lean_stringToMessageData(v___x_6581_);
    return v___x_6582_;
}
pub unsafe fn _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_6584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6584_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_;
    v___x_6585_ = l_Lean_stringToMessageData(v___x_6584_);
    return v___x_6585_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(
    mut v___x_6586_: *mut leanh::LeanObject,
    mut v_decl_6587_: *mut leanh::LeanObject,
    mut v___y_6588_: *mut leanh::LeanObject,
    mut v___y_6589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6591_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
    v___x_6592_ = l_Lean_MessageData_ofName(v___x_6586_);
    v___x_6593_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6593_, 0, v___x_6591_);
    leanh::lean_ctor_set(v___x_6593_, 1, v___x_6592_);
    v___x_6594_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_);
    v___x_6595_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6595_, 0, v___x_6593_);
    leanh::lean_ctor_set(v___x_6595_, 1, v___x_6594_);
    v___x_6596_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg(v___x_6595_, v___y_6588_, v___y_6589_);
    return v___x_6596_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(
    mut v___x_6597_: *mut leanh::LeanObject,
    mut v_decl_6598_: *mut leanh::LeanObject,
    mut v___y_6599_: *mut leanh::LeanObject,
    mut v___y_6600_: *mut leanh::LeanObject,
    mut v___y_6601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6602_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___lam__2_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_(v___x_6597_, v_decl_6598_, v___y_6599_, v___y_6600_);
    leanh::lean_dec(v___y_6600_);
    leanh::lean_dec_ref(v___y_6599_);
    leanh::lean_dec(v_decl_6598_);
    return v_res_6602_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_6683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6683_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__32_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_;
    v___x_6684_ = l_Lean_registerBuiltinAttribute(v___x_6683_);
    return v___x_6684_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(
    mut v_a_6685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6686_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_();
    return v_res_6686_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0(
    mut v_00_u03b1_6687_: *mut leanh::LeanObject,
    mut v_msg_6688_: *mut leanh::LeanObject,
    mut v___y_6689_: *mut leanh::LeanObject,
    mut v___y_6690_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6692_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___redArg(v_msg_6688_, v___y_6689_, v___y_6690_);
    return v___x_6692_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b1_6693_: *mut leanh::LeanObject,
    mut v_msg_6694_: *mut leanh::LeanObject,
    mut v___y_6695_: *mut leanh::LeanObject,
    mut v___y_6696_: *mut leanh::LeanObject,
    mut v___y_6697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6698_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__0(v_00_u03b1_6693_, v_msg_6694_, v___y_6695_, v___y_6696_);
    leanh::lean_dec(v___y_6696_);
    leanh::lean_dec_ref(v___y_6695_);
    return v_res_6698_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1(
    mut v_00_u03b1_6699_: *mut leanh::LeanObject,
    mut v_name_6700_: *mut leanh::LeanObject,
    mut v_kind_6701_: u8,
    mut v___y_6702_: *mut leanh::LeanObject,
    mut v___y_6703_: *mut leanh::LeanObject,
    mut v___y_6704_: *mut leanh::LeanObject,
    mut v___y_6705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6707_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___redArg(v_name_6700_, v_kind_6701_, v___y_6702_, v___y_6703_, v___y_6704_, v___y_6705_);
    return v___x_6707_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1___boxed(
    mut v_00_u03b1_6708_: *mut leanh::LeanObject,
    mut v_name_6709_: *mut leanh::LeanObject,
    mut v_kind_6710_: *mut leanh::LeanObject,
    mut v___y_6711_: *mut leanh::LeanObject,
    mut v___y_6712_: *mut leanh::LeanObject,
    mut v___y_6713_: *mut leanh::LeanObject,
    mut v___y_6714_: *mut leanh::LeanObject,
    mut v___y_6715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_6716_: u8 = 0;
    let mut v_res_6717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_6716_ = (leanh::lean_unbox(v_kind_6710_) as u8);
    v_res_6717_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2__spec__1(v_00_u03b1_6708_, v_name_6709_, v_kind_boxed_6716_, v___y_6711_, v___y_6712_, v___y_6713_, v___y_6714_);
    leanh::lean_dec(v___y_6714_);
    leanh::lean_dec_ref(v___y_6713_);
    leanh::lean_dec(v___y_6712_);
    leanh::lean_dec_ref(v___y_6711_);
    return v_res_6717_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_6720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6720_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_;
    v___x_6721_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1___closed__0_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_;
    v___x_6722_ = l_Lean_addBuiltinDocString(v___x_6720_, v___x_6721_);
    return v___x_6722_;
}
pub unsafe fn l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2____boxed(
    mut v_a_6723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6724_ = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_();
    return v_res_6724_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Constructions_CtorElim(
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
    res = runtime_initialize_Lean_Meta_CompletionName(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_NatTable(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_App(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn___regBuiltin___private_Lean_Meta_Constructions_CtorElim_0__Lean_initFn_docString__1_00___x40_Lean_Meta_Constructions_CtorElim_299025572____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Constructions_CtorElim(
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
pub unsafe fn initialize_Lean_Meta_Constructions_CtorElim(
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
    res = initialize_Lean_Meta_CompletionName(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Constructions_CtorIdx(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_NatTable(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_App(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_CtorElim(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Constructions_CtorElim(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Constructions_CtorElim(builtin);
}