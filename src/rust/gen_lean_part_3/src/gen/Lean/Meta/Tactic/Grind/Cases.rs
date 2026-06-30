// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Cases
// Imports: Lean.Meta.Tactic.Cases Lean.Meta.Tactic.Grind.Extension
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_set, lean_array_size,
    lean_array_to_list, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
    lean_infer_type, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_uint64_of_nat, lean_uint64_to_usize, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_land, lean_usize_mul,
    lean_usize_of_nat, lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub,
    lean_usize_to_nat, lean_whnf,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_eraseIdx___redArg;
use crate::r#gen::Init::Prelude::{l_Lean_Name_num___override, l_Lean_replaceRef};
use crate::r#gen::Lean::AuxRecursor::l_Lean_mkCasesOnName;
use crate::r#gen::Lean::CoreM::l_Lean_Core_mkFreshUserName;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::{l_Lean_NameSet_contains, l_Lean_NameSet_ofList};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_isUnaryNode___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_fvarId_x21, l_Lean_Expr_getAppFn,
    l_Lean_Expr_mvarId_x21, l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash,
    l_Lean_mkAppN, l_Lean_mkFVar,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalContext_setKind, l_Lean_LocalDecl_index, l_Lean_LocalDecl_type,
    lean_local_ctx_num_indices,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_indentExpr,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_FVarId_getDecl___redArg,
    l_Lean_Meta_isInductivePredicate_x3f, l_Lean_Meta_mkFreshExprMVarAt,
};
use crate::r#gen::Lean::Meta::InferType::{l_Lean_Meta_isProof, l_Lean_Meta_isProp};
use crate::r#gen::Lean::Meta::RecursorInfo::{
    l_Lean_Meta_RecursorInfo_numIndices, l_Lean_Meta_RecursorInfo_numMinors,
    l_Lean_Meta_mkRecursorInfo,
};
use crate::r#gen::Lean::Meta::Tactic::Assert::{l_Lean_MVarId_assert, l_Lean_MVarId_assertExt};
use crate::r#gen::Lean::Meta::Tactic::Cases::{
    initialize_Lean_Meta_Tactic_Cases, l_Lean_Meta_generalizeIndices_x27,
    runtime_initialize_Lean_Meta_Tactic_Cases,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Extension::{
    initialize_Lean_Meta_Tactic_Grind_Extension,
    l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Extension,
};
use crate::r#gen::Lean::Meta::Tactic::Induction::l_Lean_Meta_mkRecursorAppPrefix;
use crate::r#gen::Lean::Meta::Tactic::Intro::l_Lean_Meta_intro1Core;
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getTag, l_Lean_Meta_throwTacticEx___redArg,
};
use crate::r#gen::Lean::MonadEnv::l_Lean_isInductiveCore_x3f;
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
pub static l_Lean_Meta_Grind_instInhabitedCasesEntry_default___closed__0_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        0 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_instInhabitedCasesEntry_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instInhabitedCasesEntry_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instInhabitedCasesEntry_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instInhabitedCasesEntry_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_instInhabitedCasesEntry: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_instInhabitedCasesEntry_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__0_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [65, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__0_value) as *mut leanh::LeanObject,9743492140944907313 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__2_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [69, 120, 105, 115, 116, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__2_value) as *mut leanh::LeanObject,5086165725197901121 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__4_value) as *mut leanh::LeanObject,11870096045526947150 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__6_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [70, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__6_value) as *mut leanh::LeanObject,907667957179513571 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__8_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [85, 110, 105, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__8_value) as *mut leanh::LeanObject,9833841078580172006 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__10_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [69, 109, 112, 116, 121, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__10_value) as *mut leanh::LeanObject,9673466767647953041 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__12_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__11_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__12_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__13_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__9_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__12_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__13_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__14_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__7_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__13_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__14_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__15_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__5_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__14_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__15_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__16_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__3_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__15_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__16_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__17_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__1_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__16_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__17_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__18_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__18: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___closed__0: u64 = 0;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_validateCasesAttr___closed__0_value: leanh::LeanStringObject<
    27,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 96, 91, 103, 114, 105, 110, 100, 32, 99, 97, 115,
        101, 115, 93, 96, 44, 32, 96, 0,
    ],
};
static mut l_Lean_Meta_Grind_validateCasesAttr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_validateCasesAttr___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_validateCasesAttr___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_validateCasesAttr___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_validateCasesAttr___closed__2_value: leanh::LeanStringObject<
    51,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 51,
    m_capacity: 51,
    m_length: 50,
    m_data: [
        96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105,
        118, 101, 32, 100, 97, 116, 97, 116, 121, 112, 101, 32, 111, 114, 32, 97, 110, 32, 97, 108,
        105, 97, 115, 32, 102, 111, 114, 32, 111, 110, 101, 0,
    ],
};
static mut l_Lean_Meta_Grind_validateCasesAttr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_validateCasesAttr___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_validateCasesAttr___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_validateCasesAttr___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_validateCasesAttr___closed__4_value: leanh::LeanStringObject<
    33,
> = leanh::LeanStringObject {
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
        105, 110, 118, 97, 108, 105, 100, 32, 96, 91, 103, 114, 105, 110, 100, 32, 99, 97, 115,
        101, 115, 32, 101, 97, 103, 101, 114, 93, 96, 44, 32, 96, 0,
    ],
};
static mut l_Lean_Meta_Grind_validateCasesAttr___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_validateCasesAttr___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_validateCasesAttr___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_validateCasesAttr___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_validateCasesAttr___closed__6_value: leanh::LeanStringObject<
    64,
> = leanh::LeanStringObject {
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
        96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 110, 111, 110, 45, 114, 101, 99, 117, 114,
        115, 105, 118, 101, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 100, 97, 116, 97,
        116, 121, 112, 101, 32, 111, 114, 32, 97, 110, 32, 97, 108, 105, 97, 115, 32, 102, 111,
        114, 32, 111, 110, 101, 0,
    ],
};
static mut l_Lean_Meta_Grind_validateCasesAttr___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_validateCasesAttr___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_validateCasesAttr___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_validateCasesAttr___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__0_value:
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
static mut l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__2_value:
    leanh::LeanStringObject<70> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 70,
    m_capacity: 70,
    m_length: 69,
    m_data: [
        96, 32, 105, 115, 32, 109, 97, 114, 107, 101, 100, 32, 97, 115, 32, 97, 32, 98, 117, 105,
        108, 116, 45, 105, 110, 32, 99, 97, 115, 101, 45, 115, 112, 108, 105, 116, 32, 102, 111,
        114, 32, 96, 103, 114, 105, 110, 100, 96, 32, 97, 110, 100, 32, 99, 97, 110, 110, 111, 116,
        32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0,
    ],
};
static mut l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__1_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 97, 115, 101, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__0_value) as *mut leanh::LeanObject,15947788021050471391 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__1_value) as *mut leanh::LeanObject,15933525574839428776 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__3_value: leanh::LeanStringObject<44> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [40, 110, 111, 110, 45, 114, 101, 99, 117, 114, 115, 105, 118, 101, 41, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 116, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__0_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 116, 121, 112, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_cases___lam__0___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_Grind_cases___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_cases___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_cases___lam__0___closed__1_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_cases___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_cases___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_cases___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__0_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__2_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__4_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__6_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__8_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__10_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__12_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_cases___lam__1___closed__0_value: leanh::LeanStringObject<2> =
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
static mut l_Lean_Meta_Grind_cases___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_cases___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_cases___lam__1___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_cases___lam__1___closed__0_value)
                as *mut leanh::LeanObject,
            13655884332201764339 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_cases___lam__1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_cases___lam__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_cases___lam__1___closed__2_value: leanh::LeanStringObject<2> =
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
        m_data: [104, 0],
    };
static mut l_Lean_Meta_Grind_cases___lam__1___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_cases___lam__1___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_cases___lam__1___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_cases___lam__1___closed__2_value)
                as *mut leanh::LeanObject,
            8738205681931236784 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_cases___lam__1___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_cases___lam__1___closed__3_value)
        as *mut leanh::LeanObject;
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2018_ =
        l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__17;
    v___x_2019_ = l_Lean_NameSet_ofList(v___x_2018_);
    return v___x_2019_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases()
-> *mut leanh::LeanObject {
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2020_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__18), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__18_once), _init_l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases___closed__18);
    return v___x_2020_;
}
pub unsafe fn l_Lean_Meta_Grind_isBuiltinEagerCases(
    mut v_declName_2021_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: u8 = 0;
    v___x_2022_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases;
    v___x_2023_ = l_Lean_NameSet_contains(v___x_2022_, v_declName_2021_);
    return v___x_2023_;
}
pub unsafe fn l_Lean_Meta_Grind_isBuiltinEagerCases___boxed(
    mut v_declName_2024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2025_: u8 = 0;
    let mut v_r_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2025_ = l_Lean_Meta_Grind_isBuiltinEagerCases(v_declName_2024_);
    leanh::lean_dec(v_declName_2024_);
    v_r_2026_ = leanh::lean_box((v_res_2025_) as usize);
    return v_r_2026_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___redArg(
    mut v_keys_2027_: *mut leanh::LeanObject,
    mut v_i_2028_: *mut leanh::LeanObject,
    mut v_k_2029_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: u8 = 0;
    let mut v_k_x27_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: u8 = 0;
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2030_ = lean_array_get_size(v_keys_2027_);
                v___x_2031_ = lean_nat_dec_lt(v_i_2028_, v___x_2030_);
                if v___x_2031_ == 0 {
                    leanh::lean_dec(v_i_2028_);
                    return v___x_2031_;
                } else {
                    v_k_x27_2032_ = lean_array_fget_borrowed(v_keys_2027_, v_i_2028_);
                    v___x_2033_ = lean_name_eq(v_k_2029_, v_k_x27_2032_);
                    if v___x_2033_ == 0 {
                        v___x_2034_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2035_ = lean_nat_add(v_i_2028_, v___x_2034_);
                        leanh::lean_dec(v_i_2028_);
                        v_i_2028_ = v___x_2035_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_i_2028_);
                        return v___x_2033_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_2037_: *mut leanh::LeanObject,
    mut v_i_2038_: *mut leanh::LeanObject,
    mut v_k_2039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2040_: u8 = 0;
    let mut v_r_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2040_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___redArg(v_keys_2037_, v_i_2038_, v_k_2039_);
    leanh::lean_dec(v_k_2039_);
    leanh::lean_dec_ref(v_keys_2037_);
    v_r_2041_ = leanh::lean_box((v_res_2040_) as usize);
    return v_r_2041_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_2042_: usize = 0;
    let mut v___x_2043_: usize = 0;
    let mut v___x_2044_: usize = 0;
    v___x_2042_ = 5usize;
    v___x_2043_ = 1usize;
    v___x_2044_ = lean_usize_shift_left(v___x_2043_, v___x_2042_);
    return v___x_2044_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_2045_: usize = 0;
    let mut v___x_2046_: usize = 0;
    let mut v___x_2047_: usize = 0;
    v___x_2045_ = 1usize;
    v___x_2046_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__0);
    v___x_2047_ = lean_usize_sub(v___x_2046_, v___x_2045_);
    return v___x_2047_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg(
    mut v_x_2048_: *mut leanh::LeanObject,
    mut v_x_2049_: usize,
    mut v_x_2050_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_es_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: usize = 0;
    let mut v___x_2054_: usize = 0;
    let mut v___x_2055_: usize = 0;
    let mut v_j_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: u8 = 0;
    let mut v_node_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: usize = 0;
    let mut v___x_2063_: u8 = 0;
    let mut v_ks_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2048_) == 0 {
                    v_es_2051_ = leanh::lean_ctor_get(v_x_2048_, 0);
                    v___x_2052_ = leanh::lean_box(2);
                    v___x_2053_ = 5usize;
                    v___x_2054_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__1);
                    v___x_2055_ = lean_usize_land(v_x_2049_, v___x_2054_);
                    v_j_2056_ = lean_usize_to_nat(v___x_2055_);
                    v___x_2057_ = lean_array_get_borrowed(v___x_2052_, v_es_2051_, v_j_2056_);
                    leanh::lean_dec(v_j_2056_);
                    match leanh::lean_obj_tag(v___x_2057_) {
                        0 => {
                            v_key_2058_ = leanh::lean_ctor_get(v___x_2057_, 0);
                            v___x_2059_ = lean_name_eq(v_x_2050_, v_key_2058_);
                            return v___x_2059_;
                        }
                        1 => {
                            v_node_2060_ = leanh::lean_ctor_get(v___x_2057_, 0);
                            v___x_2061_ = lean_usize_shift_right(v_x_2049_, v___x_2053_);
                            v_x_2048_ = v_node_2060_;
                            v_x_2049_ = v___x_2061_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2063_ = 0;
                            return v___x_2063_;
                        }
                    }
                } else {
                    v_ks_2064_ = leanh::lean_ctor_get(v_x_2048_, 0);
                    v___x_2065_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2066_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___redArg(v_ks_2064_, v___x_2065_, v_x_2050_);
                    return v___x_2066_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___boxed(
    mut v_x_2067_: *mut leanh::LeanObject,
    mut v_x_2068_: *mut leanh::LeanObject,
    mut v_x_2069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_139__boxed_2070_: usize = 0;
    let mut v_res_2071_: u8 = 0;
    let mut v_r_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_139__boxed_2070_ = leanh::lean_unbox_usize(v_x_2068_);
    leanh::lean_dec(v_x_2068_);
    v_res_2071_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg(v_x_2067_, v_x_139__boxed_2070_, v_x_2069_);
    leanh::lean_dec(v_x_2069_);
    leanh::lean_dec_ref(v_x_2067_);
    v_r_2072_ = leanh::lean_box((v_res_2071_) as usize);
    return v_r_2072_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___closed__0()
-> u64 {
    let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: u64 = 0;
    v___x_2073_ = leanh::lean_unsigned_to_nat(1723);
    v___x_2074_ = lean_uint64_of_nat(v___x_2073_);
    return v___x_2074_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg(
    mut v_x_2075_: *mut leanh::LeanObject,
    mut v_x_2076_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_2078_: u64 = 0;
    let mut v___x_2079_: usize = 0;
    let mut v___x_2080_: u8 = 0;
    let mut v___x_2081_: u64 = 0;
    let mut v_hash_2082_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2076_) == 0 {
                    v___x_2081_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___closed__0);
                    v___y_2078_ = v___x_2081_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2082_ = leanh::lean_ctor_get_uint64(
                        v_x_2076_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2078_ = v_hash_2082_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2079_ = lean_uint64_to_usize(v___y_2078_);
                v___x_2080_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg(v_x_2075_, v___x_2079_, v_x_2076_);
                return v___x_2080_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___boxed(
    mut v_x_2083_: *mut leanh::LeanObject,
    mut v_x_2084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2085_: u8 = 0;
    let mut v_r_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2085_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg(v_x_2083_, v_x_2084_);
    leanh::lean_dec(v_x_2084_);
    leanh::lean_dec_ref(v_x_2083_);
    v_r_2086_ = leanh::lean_box((v_res_2085_) as usize);
    return v_r_2086_;
}
pub unsafe fn l_Lean_Meta_Grind_CasesTypes_contains(
    mut v_s_2087_: *mut leanh::LeanObject,
    mut v_declName_2088_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2089_: u8 = 0;
    v___x_2089_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg(v_s_2087_, v_declName_2088_);
    return v___x_2089_;
}
pub unsafe fn l_Lean_Meta_Grind_CasesTypes_contains___boxed(
    mut v_s_2090_: *mut leanh::LeanObject,
    mut v_declName_2091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2092_: u8 = 0;
    let mut v_r_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2092_ = l_Lean_Meta_Grind_CasesTypes_contains(v_s_2090_, v_declName_2091_);
    leanh::lean_dec(v_declName_2091_);
    leanh::lean_dec_ref(v_s_2090_);
    v_r_2093_ = leanh::lean_box((v_res_2092_) as usize);
    return v_r_2093_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0(
    mut v_00_u03b2_2094_: *mut leanh::LeanObject,
    mut v_x_2095_: *mut leanh::LeanObject,
    mut v_x_2096_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2097_: u8 = 0;
    v___x_2097_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg(v_x_2095_, v_x_2096_);
    return v___x_2097_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___boxed(
    mut v_00_u03b2_2098_: *mut leanh::LeanObject,
    mut v_x_2099_: *mut leanh::LeanObject,
    mut v_x_2100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2101_: u8 = 0;
    let mut v_r_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2101_ =
        l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0(
            v_00_u03b2_2098_,
            v_x_2099_,
            v_x_2100_,
        );
    leanh::lean_dec(v_x_2100_);
    leanh::lean_dec_ref(v_x_2099_);
    v_r_2102_ = leanh::lean_box((v_res_2101_) as usize);
    return v_r_2102_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0(
    mut v_00_u03b2_2103_: *mut leanh::LeanObject,
    mut v_x_2104_: *mut leanh::LeanObject,
    mut v_x_2105_: usize,
    mut v_x_2106_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2107_: u8 = 0;
    v___x_2107_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg(v_x_2104_, v_x_2105_, v_x_2106_);
    return v___x_2107_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___boxed(
    mut v_00_u03b2_2108_: *mut leanh::LeanObject,
    mut v_x_2109_: *mut leanh::LeanObject,
    mut v_x_2110_: *mut leanh::LeanObject,
    mut v_x_2111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_218__boxed_2112_: usize = 0;
    let mut v_res_2113_: u8 = 0;
    let mut v_r_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_218__boxed_2112_ = leanh::lean_unbox_usize(v_x_2110_);
    leanh::lean_dec(v_x_2110_);
    v_res_2113_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0(v_00_u03b2_2108_, v_x_2109_, v_x_218__boxed_2112_, v_x_2111_);
    leanh::lean_dec(v_x_2111_);
    leanh::lean_dec_ref(v_x_2109_);
    v_r_2114_ = leanh::lean_box((v_res_2113_) as usize);
    return v_r_2114_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2115_: *mut leanh::LeanObject,
    mut v_keys_2116_: *mut leanh::LeanObject,
    mut v_vals_2117_: *mut leanh::LeanObject,
    mut v_heq_2118_: *mut leanh::LeanObject,
    mut v_i_2119_: *mut leanh::LeanObject,
    mut v_k_2120_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2121_: u8 = 0;
    v___x_2121_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___redArg(v_keys_2116_, v_i_2119_, v_k_2120_);
    return v___x_2121_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_2122_: *mut leanh::LeanObject,
    mut v_keys_2123_: *mut leanh::LeanObject,
    mut v_vals_2124_: *mut leanh::LeanObject,
    mut v_heq_2125_: *mut leanh::LeanObject,
    mut v_i_2126_: *mut leanh::LeanObject,
    mut v_k_2127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2128_: u8 = 0;
    let mut v_r_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2128_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0_spec__1(v_00_u03b2_2122_, v_keys_2123_, v_vals_2124_, v_heq_2125_, v_i_2126_, v_k_2127_);
    leanh::lean_dec(v_k_2127_);
    leanh::lean_dec_ref(v_vals_2124_);
    leanh::lean_dec_ref(v_keys_2123_);
    v_r_2129_ = leanh::lean_box((v_res_2128_) as usize);
    return v_r_2129_;
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1_spec__2(
    mut v_xs_2130_: *mut leanh::LeanObject,
    mut v_v_2131_: *mut leanh::LeanObject,
    mut v_i_2132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: u8 = 0;
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: u8 = 0;
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2133_ = lean_array_get_size(v_xs_2130_);
                v___x_2134_ = lean_nat_dec_lt(v_i_2132_, v___x_2133_);
                if v___x_2134_ == 0 {
                    leanh::lean_dec(v_i_2132_);
                    v___x_2135_ = leanh::lean_box(0);
                    return v___x_2135_;
                } else {
                    v___x_2136_ = lean_array_fget_borrowed(v_xs_2130_, v_i_2132_);
                    v___x_2137_ = lean_name_eq(v___x_2136_, v_v_2131_);
                    if v___x_2137_ == 0 {
                        v___x_2138_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2139_ = lean_nat_add(v_i_2132_, v___x_2138_);
                        leanh::lean_dec(v_i_2132_);
                        v_i_2132_ = v___x_2139_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2141_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2141_, 0, v_i_2132_);
                        return v___x_2141_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_xs_2142_: *mut leanh::LeanObject,
    mut v_v_2143_: *mut leanh::LeanObject,
    mut v_i_2144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2145_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1_spec__2(v_xs_2142_, v_v_2143_, v_i_2144_);
    leanh::lean_dec(v_v_2143_);
    leanh::lean_dec_ref(v_xs_2142_);
    return v_res_2145_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1(
    mut v_xs_2146_: *mut leanh::LeanObject,
    mut v_v_2147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2148_ = leanh::lean_unsigned_to_nat(0);
    v___x_2149_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1_spec__2(v_xs_2146_, v_v_2147_, v___x_2148_);
    return v___x_2149_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1___boxed(
    mut v_xs_2150_: *mut leanh::LeanObject,
    mut v_v_2151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2152_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1(v_xs_2150_, v_v_2151_);
    leanh::lean_dec(v_v_2151_);
    leanh::lean_dec_ref(v_xs_2150_);
    return v_res_2152_;
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg(
    mut v_x_2153_: *mut leanh::LeanObject,
    mut v_x_2154_: usize,
    mut v_x_2155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: usize = 0;
    let mut v___x_2159_: usize = 0;
    let mut v___x_2160_: usize = 0;
    let mut v_j_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: u8 = 0;
    let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2167_: u8 = 0;
    let mut v___x_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2172_: u8 = 0;
    let mut v_unused_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2176_: u8 = 0;
    let mut v_node_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2180_: u8 = 0;
    let mut v_entries_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: usize = 0;
    let mut v_newNode_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2197_: u8 = 0;
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2205_: u8 = 0;
    let mut v_isSharedCheck_2206_: u8 = 0;
    let mut v_isSharedCheck_2207_: u8 = 0;
    let mut v_unused_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2213_: u8 = 0;
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keys_x27_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vals_x27_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2224_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2153_) == 0 {
                    v_es_2156_ = leanh::lean_ctor_get(v_x_2153_, 0);
                    v___x_2157_ = leanh::lean_box(2);
                    v___x_2158_ = 5usize;
                    v___x_2159_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__1);
                    v___x_2160_ = lean_usize_land(v_x_2154_, v___x_2159_);
                    v_j_2161_ = lean_usize_to_nat(v___x_2160_);
                    v_entry_2162_ = lean_array_get(v___x_2157_, v_es_2156_, v_j_2161_);
                    match leanh::lean_obj_tag(v_entry_2162_) {
                        0 => {
                            v_key_2163_ = leanh::lean_ctor_get(v_entry_2162_, 0);
                            leanh::lean_inc(v_key_2163_);
                            leanh::lean_dec_ref_known(v_entry_2162_, 2);
                            v___x_2164_ = lean_name_eq(v_x_2155_, v_key_2163_);
                            leanh::lean_dec(v_key_2163_);
                            if v___x_2164_ == 0 {
                                leanh::lean_dec(v_j_2161_);
                                return v_x_2153_;
                            } else {
                                leanh::lean_inc_ref(v_es_2156_);
                                v_isSharedCheck_2172_ =
                                    (!leanh::lean_is_exclusive(v_x_2153_)) as u8;
                                if v_isSharedCheck_2172_ == 0 {
                                    v_unused_2173_ = leanh::lean_ctor_get(v_x_2153_, 0);
                                    leanh::lean_dec(v_unused_2173_);
                                    v___x_2166_ = v_x_2153_;
                                    v_isShared_2167_ = v_isSharedCheck_2172_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_x_2153_);
                                    v___x_2166_ = leanh::lean_box(0);
                                    v_isShared_2167_ = v_isSharedCheck_2172_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                        1 => {
                            leanh::lean_inc_ref(v_es_2156_);
                            v_isSharedCheck_2207_ =
                                (!leanh::lean_is_exclusive(v_x_2153_)) as u8;
                            if v_isSharedCheck_2207_ == 0 {
                                v_unused_2208_ = leanh::lean_ctor_get(v_x_2153_, 0);
                                leanh::lean_dec(v_unused_2208_);
                                v___x_2175_ = v_x_2153_;
                                v_isShared_2176_ = v_isSharedCheck_2207_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_dec(v_x_2153_);
                                v___x_2175_ = leanh::lean_box(0);
                                v_isShared_2176_ = v_isSharedCheck_2207_;
                                state = 3;
                                continue;
                            }
                        }
                        _ => {
                            leanh::lean_dec(v_j_2161_);
                            return v_x_2153_;
                        }
                    }
                } else {
                    v_ks_2209_ = leanh::lean_ctor_get(v_x_2153_, 0);
                    v_vs_2210_ = leanh::lean_ctor_get(v_x_2153_, 1);
                    v_isSharedCheck_2224_ = (!leanh::lean_is_exclusive(v_x_2153_)) as u8;
                    if v_isSharedCheck_2224_ == 0 {
                        v___x_2212_ = v_x_2153_;
                        v_isShared_2213_ = v_isSharedCheck_2224_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_2210_);
                        leanh::lean_inc(v_ks_2209_);
                        leanh::lean_dec(v_x_2153_);
                        v___x_2212_ = leanh::lean_box(0);
                        v_isShared_2213_ = v_isSharedCheck_2224_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2168_ = lean_array_set(v_es_2156_, v_j_2161_, v___x_2157_);
                leanh::lean_dec(v_j_2161_);
                if v_isShared_2167_ == 0 {
                    leanh::lean_ctor_set(v___x_2166_, 0, v___x_2168_);
                    v___x_2170_ = v___x_2166_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2171_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2168_);
                    v___x_2170_ = v_reuseFailAlloc_2171_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2170_;
            }
            3 => {
                v_node_2177_ = leanh::lean_ctor_get(v_entry_2162_, 0);
                v_isSharedCheck_2206_ = (!leanh::lean_is_exclusive(v_entry_2162_)) as u8;
                if v_isSharedCheck_2206_ == 0 {
                    v___x_2179_ = v_entry_2162_;
                    v_isShared_2180_ = v_isSharedCheck_2206_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_node_2177_);
                    leanh::lean_dec(v_entry_2162_);
                    v___x_2179_ = leanh::lean_box(0);
                    v_isShared_2180_ = v_isSharedCheck_2206_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_entries_2181_ = lean_array_set(v_es_2156_, v_j_2161_, v___x_2157_);
                v___x_2182_ = lean_usize_shift_right(v_x_2154_, v___x_2158_);
                v_newNode_2183_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg(v_node_2177_, v___x_2182_, v_x_2155_);
                leanh::lean_inc_ref(v_newNode_2183_);
                v___x_2184_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_2183_);
                if leanh::lean_obj_tag(v___x_2184_) == 0 {
                    if v_isShared_2180_ == 0 {
                        leanh::lean_ctor_set(v___x_2179_, 0, v_newNode_2183_);
                        v___x_2186_ = v___x_2179_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2191_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_newNode_2183_);
                        v___x_2186_ = v_reuseFailAlloc_2191_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_newNode_2183_);
                    leanh::lean_del_object(v___x_2179_);
                    v_val_2192_ = leanh::lean_ctor_get(v___x_2184_, 0);
                    leanh::lean_inc(v_val_2192_);
                    leanh::lean_dec_ref_known(v___x_2184_, 1);
                    v_fst_2193_ = leanh::lean_ctor_get(v_val_2192_, 0);
                    v_snd_2194_ = leanh::lean_ctor_get(v_val_2192_, 1);
                    v_isSharedCheck_2205_ = (!leanh::lean_is_exclusive(v_val_2192_)) as u8;
                    if v_isSharedCheck_2205_ == 0 {
                        v___x_2196_ = v_val_2192_;
                        v_isShared_2197_ = v_isSharedCheck_2205_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2194_);
                        leanh::lean_inc(v_fst_2193_);
                        leanh::lean_dec(v_val_2192_);
                        v___x_2196_ = leanh::lean_box(0);
                        v_isShared_2197_ = v_isSharedCheck_2205_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v___x_2187_ = lean_array_set(v_entries_2181_, v_j_2161_, v___x_2186_);
                leanh::lean_dec(v_j_2161_);
                if v_isShared_2176_ == 0 {
                    leanh::lean_ctor_set(v___x_2175_, 0, v___x_2187_);
                    v___x_2189_ = v___x_2175_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2190_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2187_);
                    v___x_2189_ = v_reuseFailAlloc_2190_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2189_;
            }
            7 => {
                if v_isShared_2197_ == 0 {
                    v___x_2199_ = v___x_2196_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2204_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_fst_2193_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2204_, 1, v_snd_2194_);
                    v___x_2199_ = v_reuseFailAlloc_2204_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2200_ = lean_array_set(v_entries_2181_, v_j_2161_, v___x_2199_);
                leanh::lean_dec(v_j_2161_);
                if v_isShared_2176_ == 0 {
                    leanh::lean_ctor_set(v___x_2175_, 0, v___x_2200_);
                    v___x_2202_ = v___x_2175_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2203_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2200_);
                    v___x_2202_ = v_reuseFailAlloc_2203_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2202_;
            }
            10 => {
                v___x_2214_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0_spec__1(v_ks_2209_, v_x_2155_);
                if leanh::lean_obj_tag(v___x_2214_) == 0 {
                    if v_isShared_2213_ == 0 {
                        v___x_2216_ = v___x_2212_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_2217_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_ks_2209_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2217_, 1, v_vs_2210_);
                        v___x_2216_ = v_reuseFailAlloc_2217_;
                        state = 11;
                        continue;
                    }
                } else {
                    v_val_2218_ = leanh::lean_ctor_get(v___x_2214_, 0);
                    leanh::lean_inc_n(v_val_2218_, 2);
                    leanh::lean_dec_ref_known(v___x_2214_, 1);
                    v_keys_x27_2219_ = l_Array_eraseIdx___redArg(v_ks_2209_, v_val_2218_);
                    v_vals_x27_2220_ = l_Array_eraseIdx___redArg(v_vs_2210_, v_val_2218_);
                    if v_isShared_2213_ == 0 {
                        leanh::lean_ctor_set(v___x_2212_, 1, v_vals_x27_2220_);
                        leanh::lean_ctor_set(v___x_2212_, 0, v_keys_x27_2219_);
                        v___x_2222_ = v___x_2212_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_2223_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_keys_x27_2219_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2223_, 1, v_vals_x27_2220_);
                        v___x_2222_ = v_reuseFailAlloc_2223_;
                        state = 12;
                        continue;
                    }
                }
            }
            11 => {
                return v___x_2216_;
            }
            12 => {
                return v___x_2222_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg___boxed(
    mut v_x_2225_: *mut leanh::LeanObject,
    mut v_x_2226_: *mut leanh::LeanObject,
    mut v_x_2227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_184__boxed_2228_: usize = 0;
    let mut v_res_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_184__boxed_2228_ = leanh::lean_unbox_usize(v_x_2226_);
    leanh::lean_dec(v_x_2226_);
    v_res_2229_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg(v_x_2225_, v_x_184__boxed_2228_, v_x_2227_);
    leanh::lean_dec(v_x_2227_);
    return v_res_2229_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg(
    mut v_x_2230_: *mut leanh::LeanObject,
    mut v_x_2231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2233_: u64 = 0;
    let mut v_h_2234_: usize = 0;
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: u64 = 0;
    let mut v_hash_2237_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2231_) == 0 {
                    v___x_2236_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___closed__0);
                    v___y_2233_ = v___x_2236_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2237_ = leanh::lean_ctor_get_uint64(
                        v_x_2231_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2233_ = v_hash_2237_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_h_2234_ = lean_uint64_to_usize(v___y_2233_);
                v___x_2235_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg(v_x_2230_, v_h_2234_, v_x_2231_);
                return v___x_2235_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg___boxed(
    mut v_x_2238_: *mut leanh::LeanObject,
    mut v_x_2239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2240_ =
        l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg(
            v_x_2238_, v_x_2239_,
        );
    leanh::lean_dec(v_x_2239_);
    return v_res_2240_;
}
pub unsafe fn l_Lean_Meta_Grind_CasesTypes_erase(
    mut v_s_2241_: *mut leanh::LeanObject,
    mut v_declName_2242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2243_ =
        l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg(
            v_s_2241_,
            v_declName_2242_,
        );
    return v___x_2243_;
}
pub unsafe fn l_Lean_Meta_Grind_CasesTypes_erase___boxed(
    mut v_s_2244_: *mut leanh::LeanObject,
    mut v_declName_2245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2246_ = l_Lean_Meta_Grind_CasesTypes_erase(v_s_2244_, v_declName_2245_);
    leanh::lean_dec(v_declName_2245_);
    return v_res_2246_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0(
    mut v_00_u03b2_2247_: *mut leanh::LeanObject,
    mut v_x_2248_: *mut leanh::LeanObject,
    mut v_x_2249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2250_ =
        l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg(
            v_x_2248_, v_x_2249_,
        );
    return v___x_2250_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___boxed(
    mut v_00_u03b2_2251_: *mut leanh::LeanObject,
    mut v_x_2252_: *mut leanh::LeanObject,
    mut v_x_2253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2254_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0(
        v_00_u03b2_2251_,
        v_x_2252_,
        v_x_2253_,
    );
    leanh::lean_dec(v_x_2253_);
    return v_res_2254_;
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0(
    mut v_00_u03b2_2255_: *mut leanh::LeanObject,
    mut v_x_2256_: *mut leanh::LeanObject,
    mut v_x_2257_: usize,
    mut v_x_2258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2259_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___redArg(v_x_2256_, v_x_2257_, v_x_2258_);
    return v___x_2259_;
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0___boxed(
    mut v_00_u03b2_2260_: *mut leanh::LeanObject,
    mut v_x_2261_: *mut leanh::LeanObject,
    mut v_x_2262_: *mut leanh::LeanObject,
    mut v_x_2263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_349__boxed_2264_: usize = 0;
    let mut v_res_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_349__boxed_2264_ = leanh::lean_unbox_usize(v_x_2262_);
    leanh::lean_dec(v_x_2262_);
    v_res_2265_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0_spec__0(v_00_u03b2_2260_, v_x_2261_, v_x_349__boxed_2264_, v_x_2263_);
    leanh::lean_dec(v_x_2263_);
    return v_res_2265_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_keys_2266_: *mut leanh::LeanObject,
    mut v_vals_2267_: *mut leanh::LeanObject,
    mut v_i_2268_: *mut leanh::LeanObject,
    mut v_k_2269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: u8 = 0;
    let mut v___x_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: u8 = 0;
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2270_ = lean_array_get_size(v_keys_2266_);
                v___x_2271_ = lean_nat_dec_lt(v_i_2268_, v___x_2270_);
                if v___x_2271_ == 0 {
                    leanh::lean_dec(v_i_2268_);
                    v___x_2272_ = leanh::lean_box(0);
                    return v___x_2272_;
                } else {
                    v_k_x27_2273_ = lean_array_fget_borrowed(v_keys_2266_, v_i_2268_);
                    v___x_2274_ = lean_name_eq(v_k_2269_, v_k_x27_2273_);
                    if v___x_2274_ == 0 {
                        v___x_2275_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2276_ = lean_nat_add(v_i_2268_, v___x_2275_);
                        leanh::lean_dec(v_i_2268_);
                        v_i_2268_ = v___x_2276_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2278_ = lean_array_fget_borrowed(v_vals_2267_, v_i_2268_);
                        leanh::lean_dec(v_i_2268_);
                        leanh::lean_inc(v___x_2278_);
                        v___x_2279_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2279_, 0, v___x_2278_);
                        return v___x_2279_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_2280_: *mut leanh::LeanObject,
    mut v_vals_2281_: *mut leanh::LeanObject,
    mut v_i_2282_: *mut leanh::LeanObject,
    mut v_k_2283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2284_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2280_, v_vals_2281_, v_i_2282_, v_k_2283_);
    leanh::lean_dec(v_k_2283_);
    leanh::lean_dec_ref(v_vals_2281_);
    leanh::lean_dec_ref(v_keys_2280_);
    return v_res_2284_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg(
    mut v_x_2285_: *mut leanh::LeanObject,
    mut v_x_2286_: usize,
    mut v_x_2287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: usize = 0;
    let mut v___x_2291_: usize = 0;
    let mut v___x_2292_: usize = 0;
    let mut v_j_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: u8 = 0;
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: usize = 0;
    let mut v___x_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2285_) == 0 {
                    v_es_2288_ = leanh::lean_ctor_get(v_x_2285_, 0);
                    v___x_2289_ = leanh::lean_box(2);
                    v___x_2290_ = 5usize;
                    v___x_2291_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__1);
                    v___x_2292_ = lean_usize_land(v_x_2286_, v___x_2291_);
                    v_j_2293_ = lean_usize_to_nat(v___x_2292_);
                    v___x_2294_ = lean_array_get_borrowed(v___x_2289_, v_es_2288_, v_j_2293_);
                    leanh::lean_dec(v_j_2293_);
                    match leanh::lean_obj_tag(v___x_2294_) {
                        0 => {
                            v_key_2295_ = leanh::lean_ctor_get(v___x_2294_, 0);
                            v_val_2296_ = leanh::lean_ctor_get(v___x_2294_, 1);
                            v___x_2297_ = lean_name_eq(v_x_2287_, v_key_2295_);
                            if v___x_2297_ == 0 {
                                v___x_2298_ = leanh::lean_box(0);
                                return v___x_2298_;
                            } else {
                                leanh::lean_inc(v_val_2296_);
                                v___x_2299_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_2299_, 0, v_val_2296_);
                                return v___x_2299_;
                            }
                        }
                        1 => {
                            v_node_2300_ = leanh::lean_ctor_get(v___x_2294_, 0);
                            v___x_2301_ = lean_usize_shift_right(v_x_2286_, v___x_2290_);
                            v_x_2285_ = v_node_2300_;
                            v_x_2286_ = v___x_2301_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2303_ = leanh::lean_box(0);
                            return v___x_2303_;
                        }
                    }
                } else {
                    v_ks_2304_ = leanh::lean_ctor_get(v_x_2285_, 0);
                    v_vs_2305_ = leanh::lean_ctor_get(v_x_2285_, 1);
                    v___x_2306_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2307_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___redArg(v_ks_2304_, v_vs_2305_, v___x_2306_, v_x_2287_);
                    return v___x_2307_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_2308_: *mut leanh::LeanObject,
    mut v_x_2309_: *mut leanh::LeanObject,
    mut v_x_2310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_147__boxed_2311_: usize = 0;
    let mut v_res_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_147__boxed_2311_ = leanh::lean_unbox_usize(v_x_2309_);
    leanh::lean_dec(v_x_2309_);
    v_res_2312_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg(v_x_2308_, v_x_147__boxed_2311_, v_x_2310_);
    leanh::lean_dec(v_x_2310_);
    leanh::lean_dec_ref(v_x_2308_);
    return v_res_2312_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(
    mut v_x_2313_: *mut leanh::LeanObject,
    mut v_x_2314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2316_: u64 = 0;
    let mut v___x_2317_: usize = 0;
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: u64 = 0;
    let mut v_hash_2320_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2314_) == 0 {
                    v___x_2319_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg___closed__0);
                    v___y_2316_ = v___x_2319_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2320_ = leanh::lean_ctor_get_uint64(
                        v_x_2314_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2316_ = v_hash_2320_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2317_ = lean_uint64_to_usize(v___y_2316_);
                v___x_2318_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg(v_x_2313_, v___x_2317_, v_x_2314_);
                return v___x_2318_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg___boxed(
    mut v_x_2321_: *mut leanh::LeanObject,
    mut v_x_2322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2323_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(v_x_2321_, v_x_2322_);
    leanh::lean_dec(v_x_2322_);
    leanh::lean_dec_ref(v_x_2321_);
    return v_res_2323_;
}
pub unsafe fn l_Lean_Meta_Grind_CasesTypes_find_x3f(
    mut v_s_2324_: *mut leanh::LeanObject,
    mut v_declName_2325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2326_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(v_s_2324_, v_declName_2325_);
    return v___x_2326_;
}
pub unsafe fn l_Lean_Meta_Grind_CasesTypes_find_x3f___boxed(
    mut v_s_2327_: *mut leanh::LeanObject,
    mut v_declName_2328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2329_ = l_Lean_Meta_Grind_CasesTypes_find_x3f(v_s_2327_, v_declName_2328_);
    leanh::lean_dec(v_declName_2328_);
    leanh::lean_dec_ref(v_s_2327_);
    return v_res_2329_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0(
    mut v_00_u03b2_2330_: *mut leanh::LeanObject,
    mut v_x_2331_: *mut leanh::LeanObject,
    mut v_x_2332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2333_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(v_x_2331_, v_x_2332_);
    return v___x_2333_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___boxed(
    mut v_00_u03b2_2334_: *mut leanh::LeanObject,
    mut v_x_2335_: *mut leanh::LeanObject,
    mut v_x_2336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2337_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0(
            v_00_u03b2_2334_,
            v_x_2335_,
            v_x_2336_,
        );
    leanh::lean_dec(v_x_2336_);
    leanh::lean_dec_ref(v_x_2335_);
    return v_res_2337_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0(
    mut v_00_u03b2_2338_: *mut leanh::LeanObject,
    mut v_x_2339_: *mut leanh::LeanObject,
    mut v_x_2340_: usize,
    mut v_x_2341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2342_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___redArg(v_x_2339_, v_x_2340_, v_x_2341_);
    return v___x_2342_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_2343_: *mut leanh::LeanObject,
    mut v_x_2344_: *mut leanh::LeanObject,
    mut v_x_2345_: *mut leanh::LeanObject,
    mut v_x_2346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_225__boxed_2347_: usize = 0;
    let mut v_res_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_225__boxed_2347_ = leanh::lean_unbox_usize(v_x_2345_);
    leanh::lean_dec(v_x_2345_);
    v_res_2348_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0(v_00_u03b2_2343_, v_x_2344_, v_x_225__boxed_2347_, v_x_2346_);
    leanh::lean_dec(v_x_2346_);
    leanh::lean_dec_ref(v_x_2344_);
    return v_res_2348_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2349_: *mut leanh::LeanObject,
    mut v_keys_2350_: *mut leanh::LeanObject,
    mut v_vals_2351_: *mut leanh::LeanObject,
    mut v_heq_2352_: *mut leanh::LeanObject,
    mut v_i_2353_: *mut leanh::LeanObject,
    mut v_k_2354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2355_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2350_, v_vals_2351_, v_i_2353_, v_k_2354_);
    return v___x_2355_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_2356_: *mut leanh::LeanObject,
    mut v_keys_2357_: *mut leanh::LeanObject,
    mut v_vals_2358_: *mut leanh::LeanObject,
    mut v_heq_2359_: *mut leanh::LeanObject,
    mut v_i_2360_: *mut leanh::LeanObject,
    mut v_k_2361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2362_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2356_, v_keys_2357_, v_vals_2358_, v_heq_2359_, v_i_2360_, v_k_2361_);
    leanh::lean_dec(v_k_2361_);
    leanh::lean_dec_ref(v_vals_2358_);
    leanh::lean_dec_ref(v_keys_2357_);
    return v_res_2362_;
}
pub unsafe fn l_Lean_Meta_Grind_CasesTypes_isEagerSplit(
    mut v_s_2363_: *mut leanh::LeanObject,
    mut v_declName_2364_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2365_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(v_s_2363_, v_declName_2364_);
    if leanh::lean_obj_tag(v___x_2365_) == 0 {
        let mut v___x_2366_: u8 = 0;
        v___x_2366_ = l_Lean_Meta_Grind_isBuiltinEagerCases(v_declName_2364_);
        return v___x_2366_;
    } else {
        let mut v_val_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2368_: u8 = 0;
        v_val_2367_ = leanh::lean_ctor_get(v___x_2365_, 0);
        leanh::lean_inc(v_val_2367_);
        leanh::lean_dec_ref_known(v___x_2365_, 1);
        v___x_2368_ = (leanh::lean_unbox(v_val_2367_) as u8);
        if v___x_2368_ == 0 {
            let mut v___x_2369_: u8 = 0;
            leanh::lean_dec(v_val_2367_);
            v___x_2369_ = l_Lean_Meta_Grind_isBuiltinEagerCases(v_declName_2364_);
            return v___x_2369_;
        } else {
            let mut v___x_2370_: u8 = 0;
            v___x_2370_ = (leanh::lean_unbox(v_val_2367_) as u8);
            leanh::lean_dec(v_val_2367_);
            return v___x_2370_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_CasesTypes_isEagerSplit___boxed(
    mut v_s_2371_: *mut leanh::LeanObject,
    mut v_declName_2372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2373_: u8 = 0;
    let mut v_r_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2373_ = l_Lean_Meta_Grind_CasesTypes_isEagerSplit(v_s_2371_, v_declName_2372_);
    leanh::lean_dec(v_declName_2372_);
    leanh::lean_dec_ref(v_s_2371_);
    v_r_2374_ = leanh::lean_box((v_res_2373_) as usize);
    return v_r_2374_;
}
pub unsafe fn l_Lean_Meta_Grind_CasesTypes_isSplit(
    mut v_s_2375_: *mut leanh::LeanObject,
    mut v_declName_2376_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2377_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_CasesTypes_find_x3f_spec__0___redArg(v_s_2375_, v_declName_2376_);
    if leanh::lean_obj_tag(v___x_2377_) == 0 {
        let mut v___x_2378_: u8 = 0;
        v___x_2378_ = l_Lean_Meta_Grind_isBuiltinEagerCases(v_declName_2376_);
        return v___x_2378_;
    } else {
        let mut v___x_2379_: u8 = 0;
        leanh::lean_dec_ref_known(v___x_2377_, 1);
        v___x_2379_ = 1;
        return v___x_2379_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_CasesTypes_isSplit___boxed(
    mut v_s_2380_: *mut leanh::LeanObject,
    mut v_declName_2381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2382_: u8 = 0;
    let mut v_r_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2382_ = l_Lean_Meta_Grind_CasesTypes_isSplit(v_s_2380_, v_declName_2381_);
    leanh::lean_dec(v_declName_2381_);
    leanh::lean_dec_ref(v_s_2380_);
    v_r_2383_ = leanh::lean_box((v_res_2382_) as usize);
    return v_r_2383_;
}
pub unsafe fn l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg(
    mut v_declName_2384_: *mut leanh::LeanObject,
    mut v___y_2385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2387_ = lean_st_ref_get(v___y_2385_);
    v_env_2388_ = leanh::lean_ctor_get(v___x_2387_, 0);
    leanh::lean_inc_ref(v_env_2388_);
    leanh::lean_dec(v___x_2387_);
    v___x_2389_ = l_Lean_isInductiveCore_x3f(v_env_2388_, v_declName_2384_);
    v___x_2390_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2390_, 0, v___x_2389_);
    return v___x_2390_;
}
pub unsafe fn l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg___boxed(
    mut v_declName_2391_: *mut leanh::LeanObject,
    mut v___y_2392_: *mut leanh::LeanObject,
    mut v___y_2393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2394_ =
        l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg(
            v_declName_2391_,
            v___y_2392_,
        );
    leanh::lean_dec(v___y_2392_);
    return v_res_2394_;
}
pub unsafe fn l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0(
    mut v_declName_2395_: *mut leanh::LeanObject,
    mut v___y_2396_: *mut leanh::LeanObject,
    mut v___y_2397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2399_ =
        l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg(
            v_declName_2395_,
            v___y_2397_,
        );
    return v___x_2399_;
}
pub unsafe fn l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___boxed(
    mut v_declName_2400_: *mut leanh::LeanObject,
    mut v___y_2401_: *mut leanh::LeanObject,
    mut v___y_2402_: *mut leanh::LeanObject,
    mut v___y_2403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2404_ = l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0(
        v_declName_2400_,
        v___y_2401_,
        v___y_2402_,
    );
    leanh::lean_dec(v___y_2402_);
    leanh::lean_dec_ref(v___y_2401_);
    return v_res_2404_;
}
pub unsafe fn l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(
    mut v_declName_2405_: *mut leanh::LeanObject,
    mut v_eager_2406_: u8,
    mut v_a_2407_: *mut leanh::LeanObject,
    mut v_a_2408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2414_: u8 = 0;
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2423_: u8 = 0;
    let mut v_isRec_2424_: u8 = 0;
    let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2429_: u8 = 0;
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2432_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_declName_2405_);
                v___x_2410_ = l_Lean_isInductive_x3f___at___00Lean_Meta_Grind_isCasesAttrCandidate_x3f_spec__0___redArg(v_declName_2405_, v_a_2408_);
                v_a_2411_ = leanh::lean_ctor_get(v___x_2410_, 0);
                v_isSharedCheck_2432_ = (!leanh::lean_is_exclusive(v___x_2410_)) as u8;
                if v_isSharedCheck_2432_ == 0 {
                    v___x_2413_ = v___x_2410_;
                    v_isShared_2414_ = v_isSharedCheck_2432_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2411_);
                    leanh::lean_dec(v___x_2410_);
                    v___x_2413_ = leanh::lean_box(0);
                    v_isShared_2414_ = v_isSharedCheck_2432_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_2411_) == 1 {
                    v_val_2420_ = leanh::lean_ctor_get(v_a_2411_, 0);
                    v_isSharedCheck_2429_ = (!leanh::lean_is_exclusive(v_a_2411_)) as u8;
                    if v_isSharedCheck_2429_ == 0 {
                        v___x_2422_ = v_a_2411_;
                        v_isShared_2423_ = v_isSharedCheck_2429_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2420_);
                        leanh::lean_dec(v_a_2411_);
                        v___x_2422_ = leanh::lean_box(0);
                        v_isShared_2423_ = v_isSharedCheck_2429_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2413_);
                    leanh::lean_dec(v_a_2411_);
                    leanh::lean_dec(v_declName_2405_);
                    v___x_2430_ = leanh::lean_box(0);
                    v___x_2431_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2431_, 0, v___x_2430_);
                    return v___x_2431_;
                }
            }
            2 => {
                v___x_2416_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2416_, 0, v_declName_2405_);
                if v_isShared_2414_ == 0 {
                    leanh::lean_ctor_set(v___x_2413_, 0, v___x_2416_);
                    v___x_2418_ = v___x_2413_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2419_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2416_);
                    v___x_2418_ = v_reuseFailAlloc_2419_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2418_;
            }
            4 => {
                v_isRec_2424_ = leanh::lean_ctor_get_uint8(
                    v_val_2420_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 6) as u32,
                );
                leanh::lean_dec(v_val_2420_);
                if v_isRec_2424_ == 0 {
                    leanh::lean_del_object(v___x_2422_);
                    state = 2;
                    continue;
                } else {
                    if v_eager_2406_ == 0 {
                        leanh::lean_del_object(v___x_2422_);
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_2413_);
                        leanh::lean_dec(v_declName_2405_);
                        v___x_2425_ = leanh::lean_box(0);
                        if v_isShared_2423_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_2422_, 0);
                            leanh::lean_ctor_set(v___x_2422_, 0, v___x_2425_);
                            v___x_2427_ = v___x_2422_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_2428_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2425_);
                            v___x_2427_ = v_reuseFailAlloc_2428_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            5 => {
                return v___x_2427_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_isCasesAttrCandidate_x3f___boxed(
    mut v_declName_2433_: *mut leanh::LeanObject,
    mut v_eager_2434_: *mut leanh::LeanObject,
    mut v_a_2435_: *mut leanh::LeanObject,
    mut v_a_2436_: *mut leanh::LeanObject,
    mut v_a_2437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_eager_boxed_2438_: u8 = 0;
    let mut v_res_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_eager_boxed_2438_ = (leanh::lean_unbox(v_eager_2434_) as u8);
    v_res_2439_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(
        v_declName_2433_,
        v_eager_boxed_2438_,
        v_a_2435_,
        v_a_2436_,
    );
    leanh::lean_dec(v_a_2436_);
    leanh::lean_dec_ref(v_a_2435_);
    return v_res_2439_;
}
pub unsafe fn l_Lean_Meta_Grind_isCasesAttrCandidate(
    mut v_declName_2440_: *mut leanh::LeanObject,
    mut v_eager_2441_: u8,
    mut v_a_2442_: *mut leanh::LeanObject,
    mut v_a_2443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2449_: u8 = 0;
    let mut v___x_2450_: u8 = 0;
    let mut v___x_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: u8 = 0;
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2460_: u8 = 0;
    let mut v_a_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2464_: u8 = 0;
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2445_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(
                    v_declName_2440_,
                    v_eager_2441_,
                    v_a_2442_,
                    v_a_2443_,
                );
                if leanh::lean_obj_tag(v___x_2445_) == 0 {
                    v_a_2446_ = leanh::lean_ctor_get(v___x_2445_, 0);
                    v_isSharedCheck_2460_ = (!leanh::lean_is_exclusive(v___x_2445_)) as u8;
                    if v_isSharedCheck_2460_ == 0 {
                        v___x_2448_ = v___x_2445_;
                        v_isShared_2449_ = v_isSharedCheck_2460_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2446_);
                        leanh::lean_dec(v___x_2445_);
                        v___x_2448_ = leanh::lean_box(0);
                        v_isShared_2449_ = v_isSharedCheck_2460_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2461_ = leanh::lean_ctor_get(v___x_2445_, 0);
                    v_isSharedCheck_2468_ = (!leanh::lean_is_exclusive(v___x_2445_)) as u8;
                    if v_isSharedCheck_2468_ == 0 {
                        v___x_2463_ = v___x_2445_;
                        v_isShared_2464_ = v_isSharedCheck_2468_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2461_);
                        leanh::lean_dec(v___x_2445_);
                        v___x_2463_ = leanh::lean_box(0);
                        v_isShared_2464_ = v_isSharedCheck_2468_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_2446_) == 0 {
                    v___x_2450_ = 0;
                    v___x_2451_ = leanh::lean_box((v___x_2450_) as usize);
                    if v_isShared_2449_ == 0 {
                        leanh::lean_ctor_set(v___x_2448_, 0, v___x_2451_);
                        v___x_2453_ = v___x_2448_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2454_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2454_, 0, v___x_2451_);
                        v___x_2453_ = v_reuseFailAlloc_2454_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_a_2446_, 1);
                    v___x_2455_ = 1;
                    v___x_2456_ = leanh::lean_box((v___x_2455_) as usize);
                    if v_isShared_2449_ == 0 {
                        leanh::lean_ctor_set(v___x_2448_, 0, v___x_2456_);
                        v___x_2458_ = v___x_2448_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2459_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2459_, 0, v___x_2456_);
                        v___x_2458_ = v_reuseFailAlloc_2459_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2453_;
            }
            3 => {
                return v___x_2458_;
            }
            4 => {
                if v_isShared_2464_ == 0 {
                    v___x_2466_ = v___x_2463_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2467_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2461_);
                    v___x_2466_ = v_reuseFailAlloc_2467_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2466_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_isCasesAttrCandidate___boxed(
    mut v_declName_2469_: *mut leanh::LeanObject,
    mut v_eager_2470_: *mut leanh::LeanObject,
    mut v_a_2471_: *mut leanh::LeanObject,
    mut v_a_2472_: *mut leanh::LeanObject,
    mut v_a_2473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_eager_boxed_2474_: u8 = 0;
    let mut v_res_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_eager_boxed_2474_ = (leanh::lean_unbox(v_eager_2470_) as u8);
    v_res_2475_ = l_Lean_Meta_Grind_isCasesAttrCandidate(
        v_declName_2469_,
        v_eager_boxed_2474_,
        v_a_2471_,
        v_a_2472_,
    );
    leanh::lean_dec(v_a_2472_);
    leanh::lean_dec_ref(v_a_2471_);
    return v_res_2475_;
}
pub unsafe fn l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(
    mut v_declName_2476_: *mut leanh::LeanObject,
    mut v_eager_2477_: u8,
    mut v_a_2478_: *mut leanh::LeanObject,
    mut v_a_2479_: *mut leanh::LeanObject,
    mut v_a_2480_: *mut leanh::LeanObject,
    mut v_a_2481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2487_: u8 = 0;
    let mut v_val_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2494_: u8 = 0;
    let mut v_a_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2498_: u8 = 0;
    let mut v___x_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2502_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2483_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(
                    v_declName_2476_,
                    v_eager_2477_,
                    v_a_2480_,
                    v_a_2481_,
                );
                if leanh::lean_obj_tag(v___x_2483_) == 0 {
                    v_a_2484_ = leanh::lean_ctor_get(v___x_2483_, 0);
                    v_isSharedCheck_2494_ = (!leanh::lean_is_exclusive(v___x_2483_)) as u8;
                    if v_isSharedCheck_2494_ == 0 {
                        v___x_2486_ = v___x_2483_;
                        v_isShared_2487_ = v_isSharedCheck_2494_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2484_);
                        leanh::lean_dec(v___x_2483_);
                        v___x_2486_ = leanh::lean_box(0);
                        v_isShared_2487_ = v_isSharedCheck_2494_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2495_ = leanh::lean_ctor_get(v___x_2483_, 0);
                    v_isSharedCheck_2502_ = (!leanh::lean_is_exclusive(v___x_2483_)) as u8;
                    if v_isSharedCheck_2502_ == 0 {
                        v___x_2497_ = v___x_2483_;
                        v_isShared_2498_ = v_isSharedCheck_2502_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2495_);
                        leanh::lean_dec(v___x_2483_);
                        v___x_2497_ = leanh::lean_box(0);
                        v_isShared_2498_ = v_isSharedCheck_2502_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_2484_) == 1 {
                    leanh::lean_del_object(v___x_2486_);
                    v_val_2488_ = leanh::lean_ctor_get(v_a_2484_, 0);
                    leanh::lean_inc(v_val_2488_);
                    leanh::lean_dec_ref_known(v_a_2484_, 1);
                    v___x_2489_ = l_Lean_Meta_isInductivePredicate_x3f(
                        v_val_2488_,
                        v_a_2478_,
                        v_a_2479_,
                        v_a_2480_,
                        v_a_2481_,
                    );
                    return v___x_2489_;
                } else {
                    leanh::lean_dec(v_a_2484_);
                    v___x_2490_ = leanh::lean_box(0);
                    if v_isShared_2487_ == 0 {
                        leanh::lean_ctor_set(v___x_2486_, 0, v___x_2490_);
                        v___x_2492_ = v___x_2486_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2493_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2490_);
                        v___x_2492_ = v_reuseFailAlloc_2493_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2492_;
            }
            3 => {
                if v_isShared_2498_ == 0 {
                    v___x_2500_ = v___x_2497_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2501_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
                    v___x_2500_ = v_reuseFailAlloc_2501_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2500_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f___boxed(
    mut v_declName_2503_: *mut leanh::LeanObject,
    mut v_eager_2504_: *mut leanh::LeanObject,
    mut v_a_2505_: *mut leanh::LeanObject,
    mut v_a_2506_: *mut leanh::LeanObject,
    mut v_a_2507_: *mut leanh::LeanObject,
    mut v_a_2508_: *mut leanh::LeanObject,
    mut v_a_2509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_eager_boxed_2510_: u8 = 0;
    let mut v_res_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_eager_boxed_2510_ = (leanh::lean_unbox(v_eager_2504_) as u8);
    v_res_2511_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(
        v_declName_2503_,
        v_eager_boxed_2510_,
        v_a_2505_,
        v_a_2506_,
        v_a_2507_,
        v_a_2508_,
    );
    leanh::lean_dec(v_a_2508_);
    leanh::lean_dec_ref(v_a_2507_);
    leanh::lean_dec(v_a_2506_);
    leanh::lean_dec_ref(v_a_2505_);
    return v_res_2511_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2512_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2512_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2513_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__0);
    v___x_2514_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2514_, 0, v___x_2513_);
    return v___x_2514_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2515_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1);
    v___x_2516_ = leanh::lean_unsigned_to_nat(0);
    v___x_2517_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_2517_, 0, v___x_2516_);
    leanh::lean_ctor_set(v___x_2517_, 1, v___x_2516_);
    leanh::lean_ctor_set(v___x_2517_, 2, v___x_2516_);
    leanh::lean_ctor_set(v___x_2517_, 3, v___x_2516_);
    leanh::lean_ctor_set(v___x_2517_, 4, v___x_2515_);
    leanh::lean_ctor_set(v___x_2517_, 5, v___x_2515_);
    leanh::lean_ctor_set(v___x_2517_, 6, v___x_2515_);
    leanh::lean_ctor_set(v___x_2517_, 7, v___x_2515_);
    leanh::lean_ctor_set(v___x_2517_, 8, v___x_2515_);
    leanh::lean_ctor_set(v___x_2517_, 9, v___x_2515_);
    return v___x_2517_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2518_ = leanh::lean_unsigned_to_nat(32);
    v___x_2519_ = lean_mk_empty_array_with_capacity(v___x_2518_);
    v___x_2520_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2520_, 0, v___x_2519_);
    return v___x_2520_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2521_: usize = 0;
    let mut v___x_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2521_ = 5usize;
    v___x_2522_ = leanh::lean_unsigned_to_nat(0);
    v___x_2523_ = leanh::lean_unsigned_to_nat(32);
    v___x_2524_ = lean_mk_empty_array_with_capacity(v___x_2523_);
    v___x_2525_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__3);
    v___x_2526_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_2526_, 0, v___x_2525_);
    leanh::lean_ctor_set(v___x_2526_, 1, v___x_2524_);
    leanh::lean_ctor_set(v___x_2526_, 2, v___x_2522_);
    leanh::lean_ctor_set(v___x_2526_, 3, v___x_2522_);
    leanh::lean_ctor_set_usize(v___x_2526_, 4, v___x_2521_);
    return v___x_2526_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2527_ = leanh::lean_box(1);
    v___x_2528_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__4);
    v___x_2529_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__1);
    v___x_2530_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2530_, 0, v___x_2529_);
    leanh::lean_ctor_set(v___x_2530_, 1, v___x_2528_);
    leanh::lean_ctor_set(v___x_2530_, 2, v___x_2527_);
    return v___x_2530_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0(
    mut v_msgData_2531_: *mut leanh::LeanObject,
    mut v___y_2532_: *mut leanh::LeanObject,
    mut v___y_2533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2535_ = lean_st_ref_get(v___y_2533_);
    v_env_2536_ = leanh::lean_ctor_get(v___x_2535_, 0);
    leanh::lean_inc_ref(v_env_2536_);
    leanh::lean_dec(v___x_2535_);
    v_options_2537_ = leanh::lean_ctor_get(v___y_2532_, 2);
    v___x_2538_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2);
    v___x_2539_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5);
    leanh::lean_inc_ref(v_options_2537_);
    v___x_2540_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2540_, 0, v_env_2536_);
    leanh::lean_ctor_set(v___x_2540_, 1, v___x_2538_);
    leanh::lean_ctor_set(v___x_2540_, 2, v___x_2539_);
    leanh::lean_ctor_set(v___x_2540_, 3, v_options_2537_);
    v___x_2541_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2541_, 0, v___x_2540_);
    leanh::lean_ctor_set(v___x_2541_, 1, v_msgData_2531_);
    v___x_2542_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2542_, 0, v___x_2541_);
    return v___x_2542_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___boxed(
    mut v_msgData_2543_: *mut leanh::LeanObject,
    mut v___y_2544_: *mut leanh::LeanObject,
    mut v___y_2545_: *mut leanh::LeanObject,
    mut v___y_2546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2547_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0(v_msgData_2543_, v___y_2544_, v___y_2545_);
    leanh::lean_dec(v___y_2545_);
    leanh::lean_dec_ref(v___y_2544_);
    return v_res_2547_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(
    mut v_msg_2548_: *mut leanh::LeanObject,
    mut v___y_2549_: *mut leanh::LeanObject,
    mut v___y_2550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2557_: u8 = 0;
    let mut v___x_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2562_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2552_ = leanh::lean_ctor_get(v___y_2549_, 5);
                v___x_2553_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0(v_msg_2548_, v___y_2549_, v___y_2550_);
                v_a_2554_ = leanh::lean_ctor_get(v___x_2553_, 0);
                v_isSharedCheck_2562_ = (!leanh::lean_is_exclusive(v___x_2553_)) as u8;
                if v_isSharedCheck_2562_ == 0 {
                    v___x_2556_ = v___x_2553_;
                    v_isShared_2557_ = v_isSharedCheck_2562_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2554_);
                    leanh::lean_dec(v___x_2553_);
                    v___x_2556_ = leanh::lean_box(0);
                    v_isShared_2557_ = v_isSharedCheck_2562_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_2552_);
                v___x_2558_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2558_, 0, v_ref_2552_);
                leanh::lean_ctor_set(v___x_2558_, 1, v_a_2554_);
                if v_isShared_2557_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2556_, 1);
                    leanh::lean_ctor_set(v___x_2556_, 0, v___x_2558_);
                    v___x_2560_ = v___x_2556_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2561_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2558_);
                    v___x_2560_ = v_reuseFailAlloc_2561_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2560_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg___boxed(
    mut v_msg_2563_: *mut leanh::LeanObject,
    mut v___y_2564_: *mut leanh::LeanObject,
    mut v___y_2565_: *mut leanh::LeanObject,
    mut v___y_2566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2567_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(
        v_msg_2563_,
        v___y_2564_,
        v___y_2565_,
    );
    leanh::lean_dec(v___y_2565_);
    leanh::lean_dec_ref(v___y_2564_);
    return v_res_2567_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_validateCasesAttr___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2569_ = l_Lean_Meta_Grind_validateCasesAttr___closed__0;
    v___x_2570_ = l_Lean_stringToMessageData(v___x_2569_);
    return v___x_2570_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_validateCasesAttr___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2572_ = l_Lean_Meta_Grind_validateCasesAttr___closed__2;
    v___x_2573_ = l_Lean_stringToMessageData(v___x_2572_);
    return v___x_2573_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_validateCasesAttr___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2575_ = l_Lean_Meta_Grind_validateCasesAttr___closed__4;
    v___x_2576_ = l_Lean_stringToMessageData(v___x_2575_);
    return v___x_2576_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_validateCasesAttr___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2578_ = l_Lean_Meta_Grind_validateCasesAttr___closed__6;
    v___x_2579_ = l_Lean_stringToMessageData(v___x_2578_);
    return v___x_2579_;
}
pub unsafe fn l_Lean_Meta_Grind_validateCasesAttr(
    mut v_declName_2580_: *mut leanh::LeanObject,
    mut v_eager_2581_: u8,
    mut v_a_2582_: *mut leanh::LeanObject,
    mut v_a_2583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2589_: u8 = 0;
    let mut v___x_2590_: u8 = 0;
    let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: u8 = 0;
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2608_: u8 = 0;
    let mut v_a_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2612_: u8 = 0;
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2616_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_declName_2580_);
                v___x_2585_ = l_Lean_Meta_Grind_isCasesAttrCandidate(
                    v_declName_2580_,
                    v_eager_2581_,
                    v_a_2582_,
                    v_a_2583_,
                );
                if leanh::lean_obj_tag(v___x_2585_) == 0 {
                    v_a_2586_ = leanh::lean_ctor_get(v___x_2585_, 0);
                    v_isSharedCheck_2608_ = (!leanh::lean_is_exclusive(v___x_2585_)) as u8;
                    if v_isSharedCheck_2608_ == 0 {
                        v___x_2588_ = v___x_2585_;
                        v_isShared_2589_ = v_isSharedCheck_2608_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2586_);
                        leanh::lean_dec(v___x_2585_);
                        v___x_2588_ = leanh::lean_box(0);
                        v_isShared_2589_ = v_isSharedCheck_2608_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_declName_2580_);
                    v_a_2609_ = leanh::lean_ctor_get(v___x_2585_, 0);
                    v_isSharedCheck_2616_ = (!leanh::lean_is_exclusive(v___x_2585_)) as u8;
                    if v_isSharedCheck_2616_ == 0 {
                        v___x_2611_ = v___x_2585_;
                        v_isShared_2612_ = v_isSharedCheck_2616_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2609_);
                        leanh::lean_dec(v___x_2585_);
                        v___x_2611_ = leanh::lean_box(0);
                        v_isShared_2612_ = v_isSharedCheck_2616_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2590_ = (leanh::lean_unbox(v_a_2586_) as u8);
                if v___x_2590_ == 0 {
                    leanh::lean_del_object(v___x_2588_);
                    if v_eager_2581_ == 0 {
                        leanh::lean_dec(v_a_2586_);
                        v___x_2591_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_validateCasesAttr___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_validateCasesAttr___closed__1_once
                            ),
                            _init_l_Lean_Meta_Grind_validateCasesAttr___closed__1,
                        );
                        v___x_2592_ =
                            l_Lean_MessageData_ofConstName(v_declName_2580_, v_eager_2581_);
                        v___x_2593_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2593_, 0, v___x_2591_);
                        leanh::lean_ctor_set(v___x_2593_, 1, v___x_2592_);
                        v___x_2594_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_validateCasesAttr___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_validateCasesAttr___closed__3_once
                            ),
                            _init_l_Lean_Meta_Grind_validateCasesAttr___closed__3,
                        );
                        v___x_2595_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2595_, 0, v___x_2593_);
                        leanh::lean_ctor_set(v___x_2595_, 1, v___x_2594_);
                        v___x_2596_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(v___x_2595_, v_a_2582_, v_a_2583_);
                        return v___x_2596_;
                    } else {
                        v___x_2597_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_validateCasesAttr___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_validateCasesAttr___closed__5_once
                            ),
                            _init_l_Lean_Meta_Grind_validateCasesAttr___closed__5,
                        );
                        v___x_2598_ = (leanh::lean_unbox(v_a_2586_) as u8);
                        leanh::lean_dec(v_a_2586_);
                        v___x_2599_ = l_Lean_MessageData_ofConstName(v_declName_2580_, v___x_2598_);
                        v___x_2600_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2600_, 0, v___x_2597_);
                        leanh::lean_ctor_set(v___x_2600_, 1, v___x_2599_);
                        v___x_2601_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_validateCasesAttr___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_validateCasesAttr___closed__7_once
                            ),
                            _init_l_Lean_Meta_Grind_validateCasesAttr___closed__7,
                        );
                        v___x_2602_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2602_, 0, v___x_2600_);
                        leanh::lean_ctor_set(v___x_2602_, 1, v___x_2601_);
                        v___x_2603_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(v___x_2602_, v_a_2582_, v_a_2583_);
                        return v___x_2603_;
                    }
                } else {
                    leanh::lean_dec(v_a_2586_);
                    leanh::lean_dec(v_declName_2580_);
                    v___x_2604_ = leanh::lean_box(0);
                    if v_isShared_2589_ == 0 {
                        leanh::lean_ctor_set(v___x_2588_, 0, v___x_2604_);
                        v___x_2606_ = v___x_2588_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2607_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2604_);
                        v___x_2606_ = v_reuseFailAlloc_2607_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2606_;
            }
            3 => {
                if v_isShared_2612_ == 0 {
                    v___x_2614_ = v___x_2611_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2615_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
                    v___x_2614_ = v_reuseFailAlloc_2615_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2614_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_validateCasesAttr___boxed(
    mut v_declName_2617_: *mut leanh::LeanObject,
    mut v_eager_2618_: *mut leanh::LeanObject,
    mut v_a_2619_: *mut leanh::LeanObject,
    mut v_a_2620_: *mut leanh::LeanObject,
    mut v_a_2621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_eager_boxed_2622_: u8 = 0;
    let mut v_res_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_eager_boxed_2622_ = (leanh::lean_unbox(v_eager_2618_) as u8);
    v_res_2623_ = l_Lean_Meta_Grind_validateCasesAttr(
        v_declName_2617_,
        v_eager_boxed_2622_,
        v_a_2619_,
        v_a_2620_,
    );
    leanh::lean_dec(v_a_2620_);
    leanh::lean_dec_ref(v_a_2619_);
    return v_res_2623_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0(
    mut v_00_u03b1_2624_: *mut leanh::LeanObject,
    mut v_msg_2625_: *mut leanh::LeanObject,
    mut v___y_2626_: *mut leanh::LeanObject,
    mut v___y_2627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2629_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(
        v_msg_2625_,
        v___y_2626_,
        v___y_2627_,
    );
    return v___x_2629_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___boxed(
    mut v_00_u03b1_2630_: *mut leanh::LeanObject,
    mut v_msg_2631_: *mut leanh::LeanObject,
    mut v___y_2632_: *mut leanh::LeanObject,
    mut v___y_2633_: *mut leanh::LeanObject,
    mut v___y_2634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2635_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0(
        v_00_u03b1_2630_,
        v_msg_2631_,
        v___y_2632_,
        v___y_2633_,
    );
    leanh::lean_dec(v___y_2633_);
    leanh::lean_dec_ref(v___y_2632_);
    return v_res_2635_;
}
pub unsafe fn l_Lean_Meta_Grind_CasesTypes_eraseDecl(
    mut v_s_2636_: *mut leanh::LeanObject,
    mut v_declName_2637_: *mut leanh::LeanObject,
    mut v_a_2638_: *mut leanh::LeanObject,
    mut v_a_2639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2641_: u8 = 0;
    v___x_2641_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0___redArg(v_s_2636_, v_declName_2637_);
    if v___x_2641_ == 0 {
        let mut v___x_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_s_2636_);
        v___x_2642_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(
            v_declName_2637_,
            v_a_2638_,
            v_a_2639_,
        );
        return v___x_2642_;
    } else {
        let mut v___x_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2643_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Grind_CasesTypes_erase_spec__0___redArg(v_s_2636_, v_declName_2637_);
        leanh::lean_dec(v_declName_2637_);
        v___x_2644_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2644_, 0, v___x_2643_);
        return v___x_2644_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_CasesTypes_eraseDecl___boxed(
    mut v_s_2645_: *mut leanh::LeanObject,
    mut v_declName_2646_: *mut leanh::LeanObject,
    mut v_a_2647_: *mut leanh::LeanObject,
    mut v_a_2648_: *mut leanh::LeanObject,
    mut v_a_2649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2650_ =
        l_Lean_Meta_Grind_CasesTypes_eraseDecl(v_s_2645_, v_declName_2646_, v_a_2647_, v_a_2648_);
    leanh::lean_dec(v_a_2648_);
    leanh::lean_dec_ref(v_a_2647_);
    return v_res_2650_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2652_ = l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__0;
    v___x_2653_ = l_Lean_stringToMessageData(v___x_2652_);
    return v___x_2653_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2655_ = l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__2;
    v___x_2656_ = l_Lean_stringToMessageData(v___x_2655_);
    return v___x_2656_;
}
pub unsafe fn l_Lean_Meta_Grind_ensureNotBuiltinCases(
    mut v_declName_2657_: *mut leanh::LeanObject,
    mut v_a_2658_: *mut leanh::LeanObject,
    mut v_a_2659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2661_: u8 = 0;
    v___x_2661_ = l_Lean_Meta_Grind_isBuiltinEagerCases(v_declName_2657_);
    if v___x_2661_ == 0 {
        let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_declName_2657_);
        v___x_2662_ = leanh::lean_box(0);
        v___x_2663_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2663_, 0, v___x_2662_);
        return v___x_2663_;
    } else {
        let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2665_: u8 = 0;
        let mut v___x_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2664_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1_once),
            _init_l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1,
        );
        v___x_2665_ = 0;
        v___x_2666_ = l_Lean_MessageData_ofConstName(v_declName_2657_, v___x_2665_);
        v___x_2667_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2667_, 0, v___x_2664_);
        leanh::lean_ctor_set(v___x_2667_, 1, v___x_2666_);
        v___x_2668_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__3_once),
            _init_l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__3,
        );
        v___x_2669_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2669_, 0, v___x_2667_);
        leanh::lean_ctor_set(v___x_2669_, 1, v___x_2668_);
        v___x_2670_ = l_Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0___redArg(
            v___x_2669_,
            v_a_2658_,
            v_a_2659_,
        );
        return v___x_2670_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_ensureNotBuiltinCases___boxed(
    mut v_declName_2671_: *mut leanh::LeanObject,
    mut v_a_2672_: *mut leanh::LeanObject,
    mut v_a_2673_: *mut leanh::LeanObject,
    mut v_a_2674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2675_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_declName_2671_, v_a_2672_, v_a_2673_);
    leanh::lean_dec(v_a_2673_);
    leanh::lean_dec_ref(v_a_2672_);
    return v_res_2675_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_isSimpleFVar(
    mut v_e_2676_: *mut leanh::LeanObject,
    mut v_a_2677_: *mut leanh::LeanObject,
    mut v_a_2678_: *mut leanh::LeanObject,
    mut v_a_2679_: *mut leanh::LeanObject,
    mut v_a_2680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fvarId_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2687_: u8 = 0;
    let mut v_lctx_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: u8 = 0;
    let mut v___x_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2700_: u8 = 0;
    let mut v_a_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2704_: u8 = 0;
    let mut v___x_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2708_: u8 = 0;
    let mut v___x_2709_: u8 = 0;
    let mut v___x_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_e_2676_) == 1 {
                    v_fvarId_2682_ = leanh::lean_ctor_get(v_e_2676_, 0);
                    leanh::lean_inc(v_fvarId_2682_);
                    leanh::lean_dec_ref_known(v_e_2676_, 1);
                    v___x_2683_ = l_Lean_FVarId_getDecl___redArg(
                        v_fvarId_2682_,
                        v_a_2677_,
                        v_a_2679_,
                        v_a_2680_,
                    );
                    if leanh::lean_obj_tag(v___x_2683_) == 0 {
                        v_a_2684_ = leanh::lean_ctor_get(v___x_2683_, 0);
                        v_isSharedCheck_2700_ =
                            (!leanh::lean_is_exclusive(v___x_2683_)) as u8;
                        if v_isSharedCheck_2700_ == 0 {
                            v___x_2686_ = v___x_2683_;
                            v_isShared_2687_ = v_isSharedCheck_2700_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2684_);
                            leanh::lean_dec(v___x_2683_);
                            v___x_2686_ = leanh::lean_box(0);
                            v_isShared_2687_ = v_isSharedCheck_2700_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2701_ = leanh::lean_ctor_get(v___x_2683_, 0);
                        v_isSharedCheck_2708_ =
                            (!leanh::lean_is_exclusive(v___x_2683_)) as u8;
                        if v_isSharedCheck_2708_ == 0 {
                            v___x_2703_ = v___x_2683_;
                            v_isShared_2704_ = v_isSharedCheck_2708_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2701_);
                            leanh::lean_dec(v___x_2683_);
                            v___x_2703_ = leanh::lean_box(0);
                            v_isShared_2704_ = v_isSharedCheck_2708_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_e_2676_);
                    v___x_2709_ = 0;
                    v___x_2710_ = leanh::lean_box((v___x_2709_) as usize);
                    v___x_2711_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2711_, 0, v___x_2710_);
                    return v___x_2711_;
                }
            }
            1 => {
                v_lctx_2688_ = leanh::lean_ctor_get(v_a_2677_, 2);
                v___x_2689_ = l_Lean_LocalDecl_index(v_a_2684_);
                leanh::lean_inc_ref(v_lctx_2688_);
                v___x_2690_ = lean_local_ctx_num_indices(v_lctx_2688_);
                v___x_2691_ = leanh::lean_unsigned_to_nat(1);
                v___x_2692_ = lean_nat_sub(v___x_2690_, v___x_2691_);
                leanh::lean_dec(v___x_2690_);
                v___x_2693_ = lean_nat_dec_eq(v___x_2689_, v___x_2692_);
                leanh::lean_dec(v___x_2692_);
                leanh::lean_dec(v___x_2689_);
                if v___x_2693_ == 0 {
                    leanh::lean_del_object(v___x_2686_);
                    v___x_2694_ = l_Lean_LocalDecl_type(v_a_2684_);
                    leanh::lean_dec(v_a_2684_);
                    v___x_2695_ =
                        l_Lean_Meta_isProp(v___x_2694_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_);
                    return v___x_2695_;
                } else {
                    leanh::lean_dec(v_a_2684_);
                    v___x_2696_ = leanh::lean_box((v___x_2693_) as usize);
                    if v_isShared_2687_ == 0 {
                        leanh::lean_ctor_set(v___x_2686_, 0, v___x_2696_);
                        v___x_2698_ = v___x_2686_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2699_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2699_, 0, v___x_2696_);
                        v___x_2698_ = v_reuseFailAlloc_2699_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2698_;
            }
            3 => {
                if v_isShared_2704_ == 0 {
                    v___x_2706_ = v___x_2703_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2707_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_a_2701_);
                    v___x_2706_ = v_reuseFailAlloc_2707_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2706_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_isSimpleFVar___boxed(
    mut v_e_2712_: *mut leanh::LeanObject,
    mut v_a_2713_: *mut leanh::LeanObject,
    mut v_a_2714_: *mut leanh::LeanObject,
    mut v_a_2715_: *mut leanh::LeanObject,
    mut v_a_2716_: *mut leanh::LeanObject,
    mut v_a_2717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2718_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_isSimpleFVar(
        v_e_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_,
    );
    leanh::lean_dec(v_a_2716_);
    leanh::lean_dec_ref(v_a_2715_);
    leanh::lean_dec(v_a_2714_);
    leanh::lean_dec_ref(v_a_2713_);
    return v_res_2718_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2725_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__3;
    v___x_2726_ = l_Lean_stringToMessageData(v___x_2725_);
    return v___x_2726_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg(
    mut v_mvarId_2727_: *mut leanh::LeanObject,
    mut v_e_2728_: *mut leanh::LeanObject,
    mut v_type_2729_: *mut leanh::LeanObject,
    mut v_a_2730_: *mut leanh::LeanObject,
    mut v_a_2731_: *mut leanh::LeanObject,
    mut v_a_2732_: *mut leanh::LeanObject,
    mut v_a_2733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2735_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__2;
    v___x_2736_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__4_once), _init_l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__4);
    v___x_2737_ = l_Lean_MessageData_ofExpr(v_e_2728_);
    v___x_2738_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2738_, 0, v___x_2736_);
    leanh::lean_ctor_set(v___x_2738_, 1, v___x_2737_);
    v___x_2739_ = l_Lean_indentExpr(v_type_2729_);
    v___x_2740_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2740_, 0, v___x_2738_);
    leanh::lean_ctor_set(v___x_2740_, 1, v___x_2739_);
    v___x_2741_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2741_, 0, v___x_2740_);
    v___x_2742_ = l_Lean_Meta_throwTacticEx___redArg(
        v___x_2735_,
        v_mvarId_2727_,
        v___x_2741_,
        v_a_2730_,
        v_a_2731_,
        v_a_2732_,
        v_a_2733_,
    );
    return v___x_2742_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___boxed(
    mut v_mvarId_2743_: *mut leanh::LeanObject,
    mut v_e_2744_: *mut leanh::LeanObject,
    mut v_type_2745_: *mut leanh::LeanObject,
    mut v_a_2746_: *mut leanh::LeanObject,
    mut v_a_2747_: *mut leanh::LeanObject,
    mut v_a_2748_: *mut leanh::LeanObject,
    mut v_a_2749_: *mut leanh::LeanObject,
    mut v_a_2750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2751_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg(v_mvarId_2743_, v_e_2744_, v_type_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_);
    leanh::lean_dec(v_a_2749_);
    leanh::lean_dec_ref(v_a_2748_);
    leanh::lean_dec(v_a_2747_);
    leanh::lean_dec_ref(v_a_2746_);
    return v_res_2751_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected(
    mut v_mvarId_2752_: *mut leanh::LeanObject,
    mut v_e_2753_: *mut leanh::LeanObject,
    mut v_00_u03b1_2754_: *mut leanh::LeanObject,
    mut v_type_2755_: *mut leanh::LeanObject,
    mut v_a_2756_: *mut leanh::LeanObject,
    mut v_a_2757_: *mut leanh::LeanObject,
    mut v_a_2758_: *mut leanh::LeanObject,
    mut v_a_2759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2761_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg(v_mvarId_2752_, v_e_2753_, v_type_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_);
    return v___x_2761_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___boxed(
    mut v_mvarId_2762_: *mut leanh::LeanObject,
    mut v_e_2763_: *mut leanh::LeanObject,
    mut v_00_u03b1_2764_: *mut leanh::LeanObject,
    mut v_type_2765_: *mut leanh::LeanObject,
    mut v_a_2766_: *mut leanh::LeanObject,
    mut v_a_2767_: *mut leanh::LeanObject,
    mut v_a_2768_: *mut leanh::LeanObject,
    mut v_a_2769_: *mut leanh::LeanObject,
    mut v_a_2770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2771_ =
        l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected(
            v_mvarId_2762_,
            v_e_2763_,
            v_00_u03b1_2764_,
            v_type_2765_,
            v_a_2766_,
            v_a_2767_,
            v_a_2768_,
            v_a_2769_,
        );
    leanh::lean_dec(v_a_2769_);
    leanh::lean_dec_ref(v_a_2768_);
    leanh::lean_dec(v_a_2767_);
    leanh::lean_dec_ref(v_a_2766_);
    return v_res_2771_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(
    mut v_mvarId_2772_: *mut leanh::LeanObject,
    mut v_x_2773_: *mut leanh::LeanObject,
    mut v___y_2774_: *mut leanh::LeanObject,
    mut v___y_2775_: *mut leanh::LeanObject,
    mut v___y_2776_: *mut leanh::LeanObject,
    mut v___y_2777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2783_: u8 = 0;
    let mut v___x_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2787_: u8 = 0;
    let mut v_a_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2791_: u8 = 0;
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2795_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2779_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_2772_,
                    v_x_2773_,
                    v___y_2774_,
                    v___y_2775_,
                    v___y_2776_,
                    v___y_2777_,
                );
                if leanh::lean_obj_tag(v___x_2779_) == 0 {
                    v_a_2780_ = leanh::lean_ctor_get(v___x_2779_, 0);
                    v_isSharedCheck_2787_ = (!leanh::lean_is_exclusive(v___x_2779_)) as u8;
                    if v_isSharedCheck_2787_ == 0 {
                        v___x_2782_ = v___x_2779_;
                        v_isShared_2783_ = v_isSharedCheck_2787_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2780_);
                        leanh::lean_dec(v___x_2779_);
                        v___x_2782_ = leanh::lean_box(0);
                        v_isShared_2783_ = v_isSharedCheck_2787_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2788_ = leanh::lean_ctor_get(v___x_2779_, 0);
                    v_isSharedCheck_2795_ = (!leanh::lean_is_exclusive(v___x_2779_)) as u8;
                    if v_isSharedCheck_2795_ == 0 {
                        v___x_2790_ = v___x_2779_;
                        v_isShared_2791_ = v_isSharedCheck_2795_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2788_);
                        leanh::lean_dec(v___x_2779_);
                        v___x_2790_ = leanh::lean_box(0);
                        v_isShared_2791_ = v_isSharedCheck_2795_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2783_ == 0 {
                    v___x_2785_ = v___x_2782_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2786_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_a_2780_);
                    v___x_2785_ = v_reuseFailAlloc_2786_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2785_;
            }
            3 => {
                if v_isShared_2791_ == 0 {
                    v___x_2793_ = v___x_2790_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2794_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2788_);
                    v___x_2793_ = v_reuseFailAlloc_2794_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2793_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg___boxed(
    mut v_mvarId_2796_: *mut leanh::LeanObject,
    mut v_x_2797_: *mut leanh::LeanObject,
    mut v___y_2798_: *mut leanh::LeanObject,
    mut v___y_2799_: *mut leanh::LeanObject,
    mut v___y_2800_: *mut leanh::LeanObject,
    mut v___y_2801_: *mut leanh::LeanObject,
    mut v___y_2802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2803_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(
        v_mvarId_2796_,
        v_x_2797_,
        v___y_2798_,
        v___y_2799_,
        v___y_2800_,
        v___y_2801_,
    );
    leanh::lean_dec(v___y_2801_);
    leanh::lean_dec_ref(v___y_2800_);
    leanh::lean_dec(v___y_2799_);
    leanh::lean_dec_ref(v___y_2798_);
    return v_res_2803_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5(
    mut v_00_u03b1_2804_: *mut leanh::LeanObject,
    mut v_mvarId_2805_: *mut leanh::LeanObject,
    mut v_x_2806_: *mut leanh::LeanObject,
    mut v___y_2807_: *mut leanh::LeanObject,
    mut v___y_2808_: *mut leanh::LeanObject,
    mut v___y_2809_: *mut leanh::LeanObject,
    mut v___y_2810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2812_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(
        v_mvarId_2805_,
        v_x_2806_,
        v___y_2807_,
        v___y_2808_,
        v___y_2809_,
        v___y_2810_,
    );
    return v___x_2812_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___boxed(
    mut v_00_u03b1_2813_: *mut leanh::LeanObject,
    mut v_mvarId_2814_: *mut leanh::LeanObject,
    mut v_x_2815_: *mut leanh::LeanObject,
    mut v___y_2816_: *mut leanh::LeanObject,
    mut v___y_2817_: *mut leanh::LeanObject,
    mut v___y_2818_: *mut leanh::LeanObject,
    mut v___y_2819_: *mut leanh::LeanObject,
    mut v___y_2820_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2821_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5(
        v_00_u03b1_2813_,
        v_mvarId_2814_,
        v_x_2815_,
        v___y_2816_,
        v___y_2817_,
        v___y_2818_,
        v___y_2819_,
    );
    leanh::lean_dec(v___y_2819_);
    leanh::lean_dec_ref(v___y_2818_);
    leanh::lean_dec(v___y_2817_);
    leanh::lean_dec_ref(v___y_2816_);
    return v_res_2821_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_cases_spec__4(
    mut v_as_2822_: *mut leanh::LeanObject,
    mut v_i_2823_: usize,
    mut v_stop_2824_: usize,
    mut v_b_2825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2826_: u8 = 0;
    let mut v___x_2827_: u8 = 0;
    let mut v___x_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: usize = 0;
    let mut v___x_2831_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2826_ = lean_usize_dec_eq(v_i_2823_, v_stop_2824_);
                if v___x_2826_ == 0 {
                    v___x_2827_ = 1;
                    v___x_2828_ = lean_array_uget_borrowed(v_as_2822_, v_i_2823_);
                    leanh::lean_inc(v___x_2828_);
                    v___x_2829_ = l_Lean_LocalContext_setKind(v_b_2825_, v___x_2828_, v___x_2827_);
                    v___x_2830_ = 1usize;
                    v___x_2831_ = lean_usize_add(v_i_2823_, v___x_2830_);
                    v_i_2823_ = v___x_2831_;
                    v_b_2825_ = v___x_2829_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2825_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_cases_spec__4___boxed(
    mut v_as_2833_: *mut leanh::LeanObject,
    mut v_i_2834_: *mut leanh::LeanObject,
    mut v_stop_2835_: *mut leanh::LeanObject,
    mut v_b_2836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2837_: usize = 0;
    let mut v_stop_boxed_2838_: usize = 0;
    let mut v_res_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2837_ = leanh::lean_unbox_usize(v_i_2834_);
    leanh::lean_dec(v_i_2834_);
    v_stop_boxed_2838_ = leanh::lean_unbox_usize(v_stop_2835_);
    leanh::lean_dec(v_stop_2835_);
    v_res_2839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_cases_spec__4(v_as_2833_, v_i_boxed_2837_, v_stop_boxed_2838_, v_b_2836_);
    leanh::lean_dec_ref(v_as_2833_);
    return v_res_2839_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10_spec__13___redArg(
    mut v_x_2840_: *mut leanh::LeanObject,
    mut v_x_2841_: *mut leanh::LeanObject,
    mut v_x_2842_: *mut leanh::LeanObject,
    mut v_x_2843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2848_: u8 = 0;
    let mut v___x_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: u8 = 0;
    let mut v___x_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: u8 = 0;
    let mut v___x_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2869_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2844_ = leanh::lean_ctor_get(v_x_2840_, 0);
                v_vs_2845_ = leanh::lean_ctor_get(v_x_2840_, 1);
                v_isSharedCheck_2869_ = (!leanh::lean_is_exclusive(v_x_2840_)) as u8;
                if v_isSharedCheck_2869_ == 0 {
                    v___x_2847_ = v_x_2840_;
                    v_isShared_2848_ = v_isSharedCheck_2869_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_2845_);
                    leanh::lean_inc(v_ks_2844_);
                    leanh::lean_dec(v_x_2840_);
                    v___x_2847_ = leanh::lean_box(0);
                    v_isShared_2848_ = v_isSharedCheck_2869_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2849_ = lean_array_get_size(v_ks_2844_);
                v___x_2850_ = lean_nat_dec_lt(v_x_2841_, v___x_2849_);
                if v___x_2850_ == 0 {
                    leanh::lean_dec(v_x_2841_);
                    v___x_2851_ = lean_array_push(v_ks_2844_, v_x_2842_);
                    v___x_2852_ = lean_array_push(v_vs_2845_, v_x_2843_);
                    if v_isShared_2848_ == 0 {
                        leanh::lean_ctor_set(v___x_2847_, 1, v___x_2852_);
                        leanh::lean_ctor_set(v___x_2847_, 0, v___x_2851_);
                        v___x_2854_ = v___x_2847_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2855_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2855_, 0, v___x_2851_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2855_, 1, v___x_2852_);
                        v___x_2854_ = v_reuseFailAlloc_2855_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2856_ = lean_array_fget_borrowed(v_ks_2844_, v_x_2841_);
                    v___x_2857_ = l_Lean_instBEqMVarId_beq(v_x_2842_, v_k_x27_2856_);
                    if v___x_2857_ == 0 {
                        if v_isShared_2848_ == 0 {
                            v___x_2859_ = v___x_2847_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2863_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_ks_2844_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2863_, 1, v_vs_2845_);
                            v___x_2859_ = v_reuseFailAlloc_2863_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2864_ = lean_array_fset(v_ks_2844_, v_x_2841_, v_x_2842_);
                        v___x_2865_ = lean_array_fset(v_vs_2845_, v_x_2841_, v_x_2843_);
                        leanh::lean_dec(v_x_2841_);
                        if v_isShared_2848_ == 0 {
                            leanh::lean_ctor_set(v___x_2847_, 1, v___x_2865_);
                            leanh::lean_ctor_set(v___x_2847_, 0, v___x_2864_);
                            v___x_2867_ = v___x_2847_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2868_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2864_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2868_, 1, v___x_2865_);
                            v___x_2867_ = v_reuseFailAlloc_2868_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2854_;
            }
            3 => {
                v___x_2860_ = leanh::lean_unsigned_to_nat(1);
                v___x_2861_ = lean_nat_add(v_x_2841_, v___x_2860_);
                leanh::lean_dec(v_x_2841_);
                v_x_2840_ = v___x_2859_;
                v_x_2841_ = v___x_2861_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2867_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10___redArg(
    mut v_n_2870_: *mut leanh::LeanObject,
    mut v_k_2871_: *mut leanh::LeanObject,
    mut v_v_2872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2873_ = leanh::lean_unsigned_to_nat(0);
    v___x_2874_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10_spec__13___redArg(v_n_2870_, v___x_2873_, v_k_2871_, v_v_2872_);
    return v___x_2874_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2875_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2875_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(
    mut v_x_2876_: *mut leanh::LeanObject,
    mut v_x_2877_: usize,
    mut v_x_2878_: usize,
    mut v_x_2879_: *mut leanh::LeanObject,
    mut v_x_2880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: usize = 0;
    let mut v___x_2883_: usize = 0;
    let mut v___x_2884_: usize = 0;
    let mut v___x_2885_: usize = 0;
    let mut v_j_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: u8 = 0;
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2891_: u8 = 0;
    let mut v_v_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2905_: u8 = 0;
    let mut v___x_2906_: u8 = 0;
    let mut v___x_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2912_: u8 = 0;
    let mut v_node_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2916_: u8 = 0;
    let mut v___x_2917_: usize = 0;
    let mut v___x_2918_: usize = 0;
    let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2923_: u8 = 0;
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2925_: u8 = 0;
    let mut v_unused_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2931_: u8 = 0;
    let mut v___x_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2936_: u8 = 0;
    let mut v_ks_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: usize = 0;
    let mut v___x_2943_: u8 = 0;
    let mut v___x_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: u8 = 0;
    let mut v_reuseFailAlloc_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2948_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2876_) == 0 {
                    v_es_2881_ = leanh::lean_ctor_get(v_x_2876_, 0);
                    v___x_2882_ = 5usize;
                    v___x_2883_ = 1usize;
                    v___x_2884_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_CasesTypes_contains_spec__0_spec__0___redArg___closed__1);
                    v___x_2885_ = lean_usize_land(v_x_2877_, v___x_2884_);
                    v_j_2886_ = lean_usize_to_nat(v___x_2885_);
                    v___x_2887_ = lean_array_get_size(v_es_2881_);
                    v___x_2888_ = lean_nat_dec_lt(v_j_2886_, v___x_2887_);
                    if v___x_2888_ == 0 {
                        leanh::lean_dec(v_j_2886_);
                        leanh::lean_dec(v_x_2880_);
                        leanh::lean_dec(v_x_2879_);
                        return v_x_2876_;
                    } else {
                        leanh::lean_inc_ref(v_es_2881_);
                        v_isSharedCheck_2925_ = (!leanh::lean_is_exclusive(v_x_2876_)) as u8;
                        if v_isSharedCheck_2925_ == 0 {
                            v_unused_2926_ = leanh::lean_ctor_get(v_x_2876_, 0);
                            leanh::lean_dec(v_unused_2926_);
                            v___x_2890_ = v_x_2876_;
                            v_isShared_2891_ = v_isSharedCheck_2925_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_2876_);
                            v___x_2890_ = leanh::lean_box(0);
                            v_isShared_2891_ = v_isSharedCheck_2925_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2927_ = leanh::lean_ctor_get(v_x_2876_, 0);
                    v_vs_2928_ = leanh::lean_ctor_get(v_x_2876_, 1);
                    v_isSharedCheck_2948_ = (!leanh::lean_is_exclusive(v_x_2876_)) as u8;
                    if v_isSharedCheck_2948_ == 0 {
                        v___x_2930_ = v_x_2876_;
                        v_isShared_2931_ = v_isSharedCheck_2948_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_2928_);
                        leanh::lean_inc(v_ks_2927_);
                        leanh::lean_dec(v_x_2876_);
                        v___x_2930_ = leanh::lean_box(0);
                        v_isShared_2931_ = v_isSharedCheck_2948_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2892_ = lean_array_fget(v_es_2881_, v_j_2886_);
                v___x_2893_ = leanh::lean_box(0);
                v_xs_x27_2894_ = lean_array_fset(v_es_2881_, v_j_2886_, v___x_2893_);
                match leanh::lean_obj_tag(v_v_2892_) {
                    0 => {
                        v_key_2901_ = leanh::lean_ctor_get(v_v_2892_, 0);
                        v_val_2902_ = leanh::lean_ctor_get(v_v_2892_, 1);
                        v_isSharedCheck_2912_ = (!leanh::lean_is_exclusive(v_v_2892_)) as u8;
                        if v_isSharedCheck_2912_ == 0 {
                            v___x_2904_ = v_v_2892_;
                            v_isShared_2905_ = v_isSharedCheck_2912_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2902_);
                            leanh::lean_inc(v_key_2901_);
                            leanh::lean_dec(v_v_2892_);
                            v___x_2904_ = leanh::lean_box(0);
                            v_isShared_2905_ = v_isSharedCheck_2912_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2913_ = leanh::lean_ctor_get(v_v_2892_, 0);
                        v_isSharedCheck_2923_ = (!leanh::lean_is_exclusive(v_v_2892_)) as u8;
                        if v_isSharedCheck_2923_ == 0 {
                            v___x_2915_ = v_v_2892_;
                            v_isShared_2916_ = v_isSharedCheck_2923_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_2913_);
                            leanh::lean_dec(v_v_2892_);
                            v___x_2915_ = leanh::lean_box(0);
                            v_isShared_2916_ = v_isSharedCheck_2923_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2924_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2924_, 0, v_x_2879_);
                        leanh::lean_ctor_set(v___x_2924_, 1, v_x_2880_);
                        v___y_2896_ = v___x_2924_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2897_ = lean_array_fset(v_xs_x27_2894_, v_j_2886_, v___y_2896_);
                leanh::lean_dec(v_j_2886_);
                if v_isShared_2891_ == 0 {
                    leanh::lean_ctor_set(v___x_2890_, 0, v___x_2897_);
                    v___x_2899_ = v___x_2890_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2900_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2900_, 0, v___x_2897_);
                    v___x_2899_ = v_reuseFailAlloc_2900_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2899_;
            }
            4 => {
                v___x_2906_ = l_Lean_instBEqMVarId_beq(v_x_2879_, v_key_2901_);
                if v___x_2906_ == 0 {
                    leanh::lean_del_object(v___x_2904_);
                    v___x_2907_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2901_,
                        v_val_2902_,
                        v_x_2879_,
                        v_x_2880_,
                    );
                    v___x_2908_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2908_, 0, v___x_2907_);
                    v___y_2896_ = v___x_2908_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_2902_);
                    leanh::lean_dec(v_key_2901_);
                    if v_isShared_2905_ == 0 {
                        leanh::lean_ctor_set(v___x_2904_, 1, v_x_2880_);
                        leanh::lean_ctor_set(v___x_2904_, 0, v_x_2879_);
                        v___x_2910_ = v___x_2904_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2911_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_x_2879_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2911_, 1, v_x_2880_);
                        v___x_2910_ = v_reuseFailAlloc_2911_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2896_ = v___x_2910_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2917_ = lean_usize_shift_right(v_x_2877_, v___x_2882_);
                v___x_2918_ = lean_usize_add(v_x_2878_, v___x_2883_);
                v___x_2919_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(v_node_2913_, v___x_2917_, v___x_2918_, v_x_2879_, v_x_2880_);
                if v_isShared_2916_ == 0 {
                    leanh::lean_ctor_set(v___x_2915_, 0, v___x_2919_);
                    v___x_2921_ = v___x_2915_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2922_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2922_, 0, v___x_2919_);
                    v___x_2921_ = v_reuseFailAlloc_2922_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2896_ = v___x_2921_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2931_ == 0 {
                    v___x_2933_ = v___x_2930_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2947_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_ks_2927_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2947_, 1, v_vs_2928_);
                    v___x_2933_ = v_reuseFailAlloc_2947_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2934_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10___redArg(v___x_2933_, v_x_2879_, v_x_2880_);
                v___x_2942_ = 7usize;
                v___x_2943_ = lean_usize_dec_le(v___x_2942_, v_x_2878_);
                if v___x_2943_ == 0 {
                    v___x_2944_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2934_);
                    v___x_2945_ = leanh::lean_unsigned_to_nat(4);
                    v___x_2946_ = lean_nat_dec_lt(v___x_2944_, v___x_2945_);
                    leanh::lean_dec(v___x_2944_);
                    v___y_2936_ = v___x_2946_;
                    state = 10;
                    continue;
                } else {
                    v___y_2936_ = v___x_2943_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2936_ == 0 {
                    v_ks_2937_ = leanh::lean_ctor_get(v_newNode_2934_, 0);
                    leanh::lean_inc_ref(v_ks_2937_);
                    v_vs_2938_ = leanh::lean_ctor_get(v_newNode_2934_, 1);
                    leanh::lean_inc_ref(v_vs_2938_);
                    leanh::lean_dec_ref(v_newNode_2934_);
                    v___x_2939_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2940_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___closed__0);
                    v___x_2941_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg(v_x_2878_, v_ks_2937_, v_vs_2938_, v___x_2939_, v___x_2940_);
                    leanh::lean_dec_ref(v_vs_2938_);
                    leanh::lean_dec_ref(v_ks_2937_);
                    return v___x_2941_;
                } else {
                    return v_newNode_2934_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg(
    mut v_depth_2949_: usize,
    mut v_keys_2950_: *mut leanh::LeanObject,
    mut v_vals_2951_: *mut leanh::LeanObject,
    mut v_i_2952_: *mut leanh::LeanObject,
    mut v_entries_2953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: u8 = 0;
    let mut v_k_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: u64 = 0;
    let mut v_h_2959_: usize = 0;
    let mut v___x_2960_: usize = 0;
    let mut v___x_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: usize = 0;
    let mut v___x_2963_: usize = 0;
    let mut v___x_2964_: usize = 0;
    let mut v_h_2965_: usize = 0;
    let mut v___x_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2954_ = lean_array_get_size(v_keys_2950_);
                v___x_2955_ = lean_nat_dec_lt(v_i_2952_, v___x_2954_);
                if v___x_2955_ == 0 {
                    leanh::lean_dec(v_i_2952_);
                    return v_entries_2953_;
                } else {
                    v_k_2956_ = lean_array_fget_borrowed(v_keys_2950_, v_i_2952_);
                    v_v_2957_ = lean_array_fget_borrowed(v_vals_2951_, v_i_2952_);
                    v___x_2958_ = l_Lean_instHashableMVarId_hash(v_k_2956_);
                    v_h_2959_ = lean_uint64_to_usize(v___x_2958_);
                    v___x_2960_ = 5usize;
                    v___x_2961_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2962_ = 1usize;
                    v___x_2963_ = lean_usize_sub(v_depth_2949_, v___x_2962_);
                    v___x_2964_ = lean_usize_mul(v___x_2960_, v___x_2963_);
                    v_h_2965_ = lean_usize_shift_right(v_h_2959_, v___x_2964_);
                    v___x_2966_ = lean_nat_add(v_i_2952_, v___x_2961_);
                    leanh::lean_dec(v_i_2952_);
                    leanh::lean_inc(v_v_2957_);
                    leanh::lean_inc(v_k_2956_);
                    v___x_2967_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(v_entries_2953_, v_h_2965_, v_depth_2949_, v_k_2956_, v_v_2957_);
                    v_i_2952_ = v___x_2966_;
                    v_entries_2953_ = v___x_2967_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg___boxed(
    mut v_depth_2969_: *mut leanh::LeanObject,
    mut v_keys_2970_: *mut leanh::LeanObject,
    mut v_vals_2971_: *mut leanh::LeanObject,
    mut v_i_2972_: *mut leanh::LeanObject,
    mut v_entries_2973_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_2974_: usize = 0;
    let mut v_res_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2974_ = leanh::lean_unbox_usize(v_depth_2969_);
    leanh::lean_dec(v_depth_2969_);
    v_res_2975_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg(v_depth_boxed_2974_, v_keys_2970_, v_vals_2971_, v_i_2972_, v_entries_2973_);
    leanh::lean_dec_ref(v_vals_2971_);
    leanh::lean_dec_ref(v_keys_2970_);
    return v_res_2975_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_x_2976_: *mut leanh::LeanObject,
    mut v_x_2977_: *mut leanh::LeanObject,
    mut v_x_2978_: *mut leanh::LeanObject,
    mut v_x_2979_: *mut leanh::LeanObject,
    mut v_x_2980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_12387__boxed_2981_: usize = 0;
    let mut v_x_12388__boxed_2982_: usize = 0;
    let mut v_res_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_12387__boxed_2981_ = leanh::lean_unbox_usize(v_x_2977_);
    leanh::lean_dec(v_x_2977_);
    v_x_12388__boxed_2982_ = leanh::lean_unbox_usize(v_x_2978_);
    leanh::lean_dec(v_x_2978_);
    v_res_2983_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(v_x_2976_, v_x_12387__boxed_2981_, v_x_12388__boxed_2982_, v_x_2979_, v_x_2980_);
    return v_res_2983_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2___redArg(
    mut v_x_2984_: *mut leanh::LeanObject,
    mut v_x_2985_: *mut leanh::LeanObject,
    mut v_x_2986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2987_: u64 = 0;
    let mut v___x_2988_: usize = 0;
    let mut v___x_2989_: usize = 0;
    let mut v___x_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2987_ = l_Lean_instHashableMVarId_hash(v_x_2985_);
    v___x_2988_ = lean_uint64_to_usize(v___x_2987_);
    v___x_2989_ = 1usize;
    v___x_2990_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(v_x_2984_, v___x_2988_, v___x_2989_, v_x_2985_, v_x_2986_);
    return v___x_2990_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg(
    mut v_mvarId_2991_: *mut leanh::LeanObject,
    mut v_val_2992_: *mut leanh::LeanObject,
    mut v___y_2993_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3003_: u8 = 0;
    let mut v_depth_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3016_: u8 = 0;
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3027_: u8 = 0;
    let mut v_isSharedCheck_3028_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2995_ = lean_st_ref_take(v___y_2993_);
                v_mctx_2996_ = leanh::lean_ctor_get(v___x_2995_, 0);
                v_cache_2997_ = leanh::lean_ctor_get(v___x_2995_, 1);
                v_zetaDeltaFVarIds_2998_ = leanh::lean_ctor_get(v___x_2995_, 2);
                v_postponed_2999_ = leanh::lean_ctor_get(v___x_2995_, 3);
                v_diag_3000_ = leanh::lean_ctor_get(v___x_2995_, 4);
                v_isSharedCheck_3028_ = (!leanh::lean_is_exclusive(v___x_2995_)) as u8;
                if v_isSharedCheck_3028_ == 0 {
                    v___x_3002_ = v___x_2995_;
                    v_isShared_3003_ = v_isSharedCheck_3028_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_3000_);
                    leanh::lean_inc(v_postponed_2999_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_2998_);
                    leanh::lean_inc(v_cache_2997_);
                    leanh::lean_inc(v_mctx_2996_);
                    leanh::lean_dec(v___x_2995_);
                    v___x_3002_ = leanh::lean_box(0);
                    v_isShared_3003_ = v_isSharedCheck_3028_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_3004_ = leanh::lean_ctor_get(v_mctx_2996_, 0);
                v_levelAssignDepth_3005_ = leanh::lean_ctor_get(v_mctx_2996_, 1);
                v_lmvarCounter_3006_ = leanh::lean_ctor_get(v_mctx_2996_, 2);
                v_mvarCounter_3007_ = leanh::lean_ctor_get(v_mctx_2996_, 3);
                v_lDecls_3008_ = leanh::lean_ctor_get(v_mctx_2996_, 4);
                v_decls_3009_ = leanh::lean_ctor_get(v_mctx_2996_, 5);
                v_userNames_3010_ = leanh::lean_ctor_get(v_mctx_2996_, 6);
                v_lAssignment_3011_ = leanh::lean_ctor_get(v_mctx_2996_, 7);
                v_eAssignment_3012_ = leanh::lean_ctor_get(v_mctx_2996_, 8);
                v_dAssignment_3013_ = leanh::lean_ctor_get(v_mctx_2996_, 9);
                v_isSharedCheck_3027_ = (!leanh::lean_is_exclusive(v_mctx_2996_)) as u8;
                if v_isSharedCheck_3027_ == 0 {
                    v___x_3015_ = v_mctx_2996_;
                    v_isShared_3016_ = v_isSharedCheck_3027_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_dAssignment_3013_);
                    leanh::lean_inc(v_eAssignment_3012_);
                    leanh::lean_inc(v_lAssignment_3011_);
                    leanh::lean_inc(v_userNames_3010_);
                    leanh::lean_inc(v_decls_3009_);
                    leanh::lean_inc(v_lDecls_3008_);
                    leanh::lean_inc(v_mvarCounter_3007_);
                    leanh::lean_inc(v_lmvarCounter_3006_);
                    leanh::lean_inc(v_levelAssignDepth_3005_);
                    leanh::lean_inc(v_depth_3004_);
                    leanh::lean_dec(v_mctx_2996_);
                    v___x_3015_ = leanh::lean_box(0);
                    v_isShared_3016_ = v_isSharedCheck_3027_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3017_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2___redArg(v_eAssignment_3012_, v_mvarId_2991_, v_val_2992_);
                if v_isShared_3016_ == 0 {
                    leanh::lean_ctor_set(v___x_3015_, 8, v___x_3017_);
                    v___x_3019_ = v___x_3015_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3026_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_depth_3004_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3026_,
                        1,
                        v_levelAssignDepth_3005_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3026_, 2, v_lmvarCounter_3006_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3026_, 3, v_mvarCounter_3007_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3026_, 4, v_lDecls_3008_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3026_, 5, v_decls_3009_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3026_, 6, v_userNames_3010_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3026_, 7, v_lAssignment_3011_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3026_, 8, v___x_3017_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3026_, 9, v_dAssignment_3013_);
                    v___x_3019_ = v_reuseFailAlloc_3026_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3003_ == 0 {
                    leanh::lean_ctor_set(v___x_3002_, 0, v___x_3019_);
                    v___x_3021_ = v___x_3002_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3025_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3025_, 0, v___x_3019_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3025_, 1, v_cache_2997_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3025_,
                        2,
                        v_zetaDeltaFVarIds_2998_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3025_, 3, v_postponed_2999_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3025_, 4, v_diag_3000_);
                    v___x_3021_ = v_reuseFailAlloc_3025_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3022_ = lean_st_ref_set(v___y_2993_, v___x_3021_);
                v___x_3023_ = leanh::lean_box(0);
                v___x_3024_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3024_, 0, v___x_3023_);
                return v___x_3024_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg___boxed(
    mut v_mvarId_3029_: *mut leanh::LeanObject,
    mut v_val_3030_: *mut leanh::LeanObject,
    mut v___y_3031_: *mut leanh::LeanObject,
    mut v___y_3032_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3033_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg(
        v_mvarId_3029_,
        v_val_3030_,
        v___y_3031_,
    );
    leanh::lean_dec(v___y_3031_);
    return v_res_3033_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3037_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__1;
    v___x_3038_ = l_Lean_MessageData_ofFormat(v___x_3037_);
    return v___x_3038_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3039_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__2_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__2);
    v___x_3040_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3040_, 0, v___x_3039_);
    return v___x_3040_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg(
    mut v_upperBound_3041_: *mut leanh::LeanObject,
    mut v___y_3042_: *mut leanh::LeanObject,
    mut v___x_3043_: *mut leanh::LeanObject,
    mut v___x_3044_: *mut leanh::LeanObject,
    mut v_a_3045_: *mut leanh::LeanObject,
    mut v_mvarId_3046_: *mut leanh::LeanObject,
    mut v_a_3047_: *mut leanh::LeanObject,
    mut v_b_3048_: *mut leanh::LeanObject,
    mut v___y_3049_: *mut leanh::LeanObject,
    mut v___y_3050_: *mut leanh::LeanObject,
    mut v___y_3051_: *mut leanh::LeanObject,
    mut v___y_3052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3054_: u8 = 0;
    let mut v___x_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3060_: u8 = 0;
    let mut v_fst_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3065_: u8 = 0;
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3072_: u8 = 0;
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: u8 = 0;
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3102_: u8 = 0;
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3106_: u8 = 0;
    let mut v___x_3107_: u8 = 0;
    let mut v___x_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3124_: u8 = 0;
    let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3128_: u8 = 0;
    let mut v_isSharedCheck_3129_: u8 = 0;
    let mut v_a_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3133_: u8 = 0;
    let mut v___x_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3137_: u8 = 0;
    let mut v_isSharedCheck_3138_: u8 = 0;
    let mut v_isSharedCheck_3139_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3054_ = lean_nat_dec_lt(v_a_3047_, v_upperBound_3041_);
                if v___x_3054_ == 0 {
                    leanh::lean_dec(v_a_3047_);
                    leanh::lean_dec(v_mvarId_3046_);
                    leanh::lean_dec(v_a_3045_);
                    leanh::lean_dec_ref(v___x_3043_);
                    leanh::lean_dec_ref(v___y_3042_);
                    v___x_3055_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3055_, 0, v_b_3048_);
                    return v___x_3055_;
                } else {
                    v_snd_3056_ = leanh::lean_ctor_get(v_b_3048_, 1);
                    v_fst_3057_ = leanh::lean_ctor_get(v_b_3048_, 0);
                    v_isSharedCheck_3139_ = (!leanh::lean_is_exclusive(v_b_3048_)) as u8;
                    if v_isSharedCheck_3139_ == 0 {
                        v___x_3059_ = v_b_3048_;
                        v_isShared_3060_ = v_isSharedCheck_3139_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3056_);
                        leanh::lean_inc(v_fst_3057_);
                        leanh::lean_dec(v_b_3048_);
                        v___x_3059_ = leanh::lean_box(0);
                        v_isShared_3060_ = v_isSharedCheck_3139_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3061_ = leanh::lean_ctor_get(v_snd_3056_, 0);
                v_snd_3062_ = leanh::lean_ctor_get(v_snd_3056_, 1);
                v_isSharedCheck_3138_ = (!leanh::lean_is_exclusive(v_snd_3056_)) as u8;
                if v_isSharedCheck_3138_ == 0 {
                    v___x_3064_ = v_snd_3056_;
                    v_isShared_3065_ = v_isSharedCheck_3138_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3062_);
                    leanh::lean_inc(v_fst_3061_);
                    leanh::lean_dec(v_snd_3056_);
                    v___x_3064_ = leanh::lean_box(0);
                    v_isShared_3065_ = v_isSharedCheck_3138_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v___y_3052_);
                leanh::lean_inc_ref(v___y_3051_);
                leanh::lean_inc(v___y_3050_);
                leanh::lean_inc_ref(v___y_3049_);
                leanh::lean_inc(v_fst_3061_);
                v___x_3066_ = lean_whnf(
                    v_fst_3061_,
                    v___y_3049_,
                    v___y_3050_,
                    v___y_3051_,
                    v___y_3052_,
                );
                if leanh::lean_obj_tag(v___x_3066_) == 0 {
                    v_a_3067_ = leanh::lean_ctor_get(v___x_3066_, 0);
                    leanh::lean_inc(v_a_3067_);
                    leanh::lean_dec_ref_known(v___x_3066_, 1);
                    v_fst_3068_ = leanh::lean_ctor_get(v_snd_3062_, 0);
                    v_snd_3069_ = leanh::lean_ctor_get(v_snd_3062_, 1);
                    v_isSharedCheck_3129_ = (!leanh::lean_is_exclusive(v_snd_3062_)) as u8;
                    if v_isSharedCheck_3129_ == 0 {
                        v___x_3071_ = v_snd_3062_;
                        v_isShared_3072_ = v_isSharedCheck_3129_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3069_);
                        leanh::lean_inc(v_fst_3068_);
                        leanh::lean_dec(v_snd_3062_);
                        v___x_3071_ = leanh::lean_box(0);
                        v_isShared_3072_ = v_isSharedCheck_3129_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3064_);
                    leanh::lean_dec(v_snd_3062_);
                    leanh::lean_dec(v_fst_3061_);
                    leanh::lean_del_object(v___x_3059_);
                    leanh::lean_dec(v_fst_3057_);
                    leanh::lean_dec(v_a_3047_);
                    leanh::lean_dec(v_mvarId_3046_);
                    leanh::lean_dec(v_a_3045_);
                    leanh::lean_dec_ref(v___x_3043_);
                    leanh::lean_dec_ref(v___y_3042_);
                    v_a_3130_ = leanh::lean_ctor_get(v___x_3066_, 0);
                    v_isSharedCheck_3137_ = (!leanh::lean_is_exclusive(v___x_3066_)) as u8;
                    if v_isSharedCheck_3137_ == 0 {
                        v___x_3132_ = v___x_3066_;
                        v_isShared_3133_ = v_isSharedCheck_3137_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3130_);
                        leanh::lean_dec(v___x_3066_);
                        v___x_3132_ = leanh::lean_box(0);
                        v_isShared_3133_ = v_isSharedCheck_3137_;
                        state = 16;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3073_ = leanh::lean_unsigned_to_nat(1);
                if leanh::lean_obj_tag(v_a_3067_) == 7 {
                    leanh::lean_dec(v_fst_3061_);
                    v_binderType_3078_ = leanh::lean_ctor_get(v_a_3067_, 1);
                    leanh::lean_inc_ref(v_binderType_3078_);
                    v_body_3079_ = leanh::lean_ctor_get(v_a_3067_, 2);
                    leanh::lean_inc_ref(v_body_3079_);
                    leanh::lean_dec_ref_known(v_a_3067_, 3);
                    v___x_3080_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3107_ = lean_nat_dec_lt(v___x_3073_, v___x_3044_);
                    if v___x_3107_ == 0 {
                        leanh::lean_inc(v_a_3045_);
                        v___y_3082_ = v_a_3045_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3069_);
                        leanh::lean_inc(v_a_3045_);
                        v___x_3108_ = l_Lean_Name_num___override(v_a_3045_, v_snd_3069_);
                        v___y_3082_ = v___x_3108_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3067_);
                    v___x_3109_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__2;
                    v___x_3110_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__3_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___closed__3);
                    leanh::lean_inc(v_mvarId_3046_);
                    v___x_3111_ = l_Lean_Meta_throwTacticEx___redArg(
                        v___x_3109_,
                        v_mvarId_3046_,
                        v___x_3110_,
                        v___y_3049_,
                        v___y_3050_,
                        v___y_3051_,
                        v___y_3052_,
                    );
                    if leanh::lean_obj_tag(v___x_3111_) == 0 {
                        leanh::lean_dec_ref_known(v___x_3111_, 1);
                        if v_isShared_3072_ == 0 {
                            v___x_3113_ = v___x_3071_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_3120_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_fst_3068_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3120_, 1, v_snd_3069_);
                            v___x_3113_ = v_reuseFailAlloc_3120_;
                            state = 11;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_3071_);
                        leanh::lean_dec(v_snd_3069_);
                        leanh::lean_dec(v_fst_3068_);
                        leanh::lean_del_object(v___x_3064_);
                        leanh::lean_dec(v_fst_3061_);
                        leanh::lean_del_object(v___x_3059_);
                        leanh::lean_dec(v_fst_3057_);
                        leanh::lean_dec(v_a_3047_);
                        leanh::lean_dec(v_mvarId_3046_);
                        leanh::lean_dec(v_a_3045_);
                        leanh::lean_dec_ref(v___x_3043_);
                        leanh::lean_dec_ref(v___y_3042_);
                        v_a_3121_ = leanh::lean_ctor_get(v___x_3111_, 0);
                        v_isSharedCheck_3128_ =
                            (!leanh::lean_is_exclusive(v___x_3111_)) as u8;
                        if v_isSharedCheck_3128_ == 0 {
                            v___x_3123_ = v___x_3111_;
                            v_isShared_3124_ = v_isSharedCheck_3128_;
                            state = 14;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3121_);
                            leanh::lean_dec(v___x_3111_);
                            v___x_3123_ = leanh::lean_box(0);
                            v_isShared_3124_ = v_isSharedCheck_3128_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v___x_3076_ = lean_nat_add(v_a_3047_, v___x_3073_);
                leanh::lean_dec(v_a_3047_);
                v_a_3047_ = v___x_3076_;
                v_b_3048_ = v_a_3075_;
                state = 0;
                continue;
            }
            5 => {
                v___x_3083_ = 2;
                leanh::lean_inc_ref(v___x_3043_);
                leanh::lean_inc_ref(v___y_3042_);
                v___x_3084_ = l_Lean_Meta_mkFreshExprMVarAt(
                    v___y_3042_,
                    v___x_3043_,
                    v_binderType_3078_,
                    v___x_3083_,
                    v___y_3082_,
                    v___x_3080_,
                    v___y_3049_,
                    v___y_3050_,
                    v___y_3051_,
                    v___y_3052_,
                );
                if leanh::lean_obj_tag(v___x_3084_) == 0 {
                    v_a_3085_ = leanh::lean_ctor_get(v___x_3084_, 0);
                    leanh::lean_inc_n(v_a_3085_, 2);
                    leanh::lean_dec_ref_known(v___x_3084_, 1);
                    v___x_3086_ = l_Lean_Expr_app___override(v_fst_3057_, v_a_3085_);
                    v___x_3087_ = l_Lean_Expr_mvarId_x21(v_a_3085_);
                    leanh::lean_dec(v_a_3085_);
                    v___x_3088_ = lean_array_push(v_fst_3068_, v___x_3087_);
                    v___x_3089_ = lean_nat_add(v_snd_3069_, v___x_3073_);
                    leanh::lean_dec(v_snd_3069_);
                    if v_isShared_3072_ == 0 {
                        leanh::lean_ctor_set(v___x_3071_, 1, v___x_3089_);
                        leanh::lean_ctor_set(v___x_3071_, 0, v___x_3088_);
                        v___x_3091_ = v___x_3071_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3098_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3088_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3098_, 1, v___x_3089_);
                        v___x_3091_ = v_reuseFailAlloc_3098_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_body_3079_);
                    leanh::lean_del_object(v___x_3071_);
                    leanh::lean_dec(v_snd_3069_);
                    leanh::lean_dec(v_fst_3068_);
                    leanh::lean_del_object(v___x_3064_);
                    leanh::lean_del_object(v___x_3059_);
                    leanh::lean_dec(v_fst_3057_);
                    leanh::lean_dec(v_a_3047_);
                    leanh::lean_dec(v_mvarId_3046_);
                    leanh::lean_dec(v_a_3045_);
                    leanh::lean_dec_ref(v___x_3043_);
                    leanh::lean_dec_ref(v___y_3042_);
                    v_a_3099_ = leanh::lean_ctor_get(v___x_3084_, 0);
                    v_isSharedCheck_3106_ = (!leanh::lean_is_exclusive(v___x_3084_)) as u8;
                    if v_isSharedCheck_3106_ == 0 {
                        v___x_3101_ = v___x_3084_;
                        v_isShared_3102_ = v_isSharedCheck_3106_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3099_);
                        leanh::lean_dec(v___x_3084_);
                        v___x_3101_ = leanh::lean_box(0);
                        v_isShared_3102_ = v_isSharedCheck_3106_;
                        state = 9;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_3065_ == 0 {
                    leanh::lean_ctor_set(v___x_3064_, 1, v___x_3091_);
                    leanh::lean_ctor_set(v___x_3064_, 0, v_body_3079_);
                    v___x_3093_ = v___x_3064_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3097_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_body_3079_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3097_, 1, v___x_3091_);
                    v___x_3093_ = v_reuseFailAlloc_3097_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3060_ == 0 {
                    leanh::lean_ctor_set(v___x_3059_, 1, v___x_3093_);
                    leanh::lean_ctor_set(v___x_3059_, 0, v___x_3086_);
                    v___x_3095_ = v___x_3059_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3096_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3096_, 0, v___x_3086_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3096_, 1, v___x_3093_);
                    v___x_3095_ = v_reuseFailAlloc_3096_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_a_3075_ = v___x_3095_;
                state = 4;
                continue;
            }
            9 => {
                if v_isShared_3102_ == 0 {
                    v___x_3104_ = v___x_3101_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3105_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3099_);
                    v___x_3104_ = v_reuseFailAlloc_3105_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3104_;
            }
            11 => {
                if v_isShared_3065_ == 0 {
                    leanh::lean_ctor_set(v___x_3064_, 1, v___x_3113_);
                    v___x_3115_ = v___x_3064_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3119_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_fst_3061_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3119_, 1, v___x_3113_);
                    v___x_3115_ = v_reuseFailAlloc_3119_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_3060_ == 0 {
                    leanh::lean_ctor_set(v___x_3059_, 1, v___x_3115_);
                    v___x_3117_ = v___x_3059_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3118_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_fst_3057_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3118_, 1, v___x_3115_);
                    v___x_3117_ = v_reuseFailAlloc_3118_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v_a_3075_ = v___x_3117_;
                state = 4;
                continue;
            }
            14 => {
                if v_isShared_3124_ == 0 {
                    v___x_3126_ = v___x_3123_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3127_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_a_3121_);
                    v___x_3126_ = v_reuseFailAlloc_3127_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3126_;
            }
            16 => {
                if v_isShared_3133_ == 0 {
                    v___x_3135_ = v___x_3132_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3136_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_a_3130_);
                    v___x_3135_ = v_reuseFailAlloc_3136_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3135_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg___boxed(
    mut v_upperBound_3140_: *mut leanh::LeanObject,
    mut v___y_3141_: *mut leanh::LeanObject,
    mut v___x_3142_: *mut leanh::LeanObject,
    mut v___x_3143_: *mut leanh::LeanObject,
    mut v_a_3144_: *mut leanh::LeanObject,
    mut v_mvarId_3145_: *mut leanh::LeanObject,
    mut v_a_3146_: *mut leanh::LeanObject,
    mut v_b_3147_: *mut leanh::LeanObject,
    mut v___y_3148_: *mut leanh::LeanObject,
    mut v___y_3149_: *mut leanh::LeanObject,
    mut v___y_3150_: *mut leanh::LeanObject,
    mut v___y_3151_: *mut leanh::LeanObject,
    mut v___y_3152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3153_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg(
        v_upperBound_3140_,
        v___y_3141_,
        v___x_3142_,
        v___x_3143_,
        v_a_3144_,
        v_mvarId_3145_,
        v_a_3146_,
        v_b_3147_,
        v___y_3148_,
        v___y_3149_,
        v___y_3150_,
        v___y_3151_,
    );
    leanh::lean_dec(v___y_3151_);
    leanh::lean_dec_ref(v___y_3150_);
    leanh::lean_dec(v___y_3149_);
    leanh::lean_dec_ref(v___y_3148_);
    leanh::lean_dec(v___x_3143_);
    leanh::lean_dec(v_upperBound_3140_);
    return v_res_3153_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_cases_spec__2(
    mut v_sz_3154_: usize,
    mut v_i_3155_: usize,
    mut v_bs_3156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3157_: u8 = 0;
    let mut v_v_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: usize = 0;
    let mut v___x_3163_: usize = 0;
    let mut v___x_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3157_ = lean_usize_dec_lt(v_i_3155_, v_sz_3154_);
                if v___x_3157_ == 0 {
                    return v_bs_3156_;
                } else {
                    v_v_3158_ = lean_array_uget(v_bs_3156_, v_i_3155_);
                    v___x_3159_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3160_ = lean_array_uset(v_bs_3156_, v_i_3155_, v___x_3159_);
                    v___x_3161_ = l_Lean_mkFVar(v_v_3158_);
                    v___x_3162_ = 1usize;
                    v___x_3163_ = lean_usize_add(v_i_3155_, v___x_3162_);
                    v___x_3164_ = lean_array_uset(v_bs_x27_3160_, v_i_3155_, v___x_3161_);
                    v_i_3155_ = v___x_3163_;
                    v_bs_3156_ = v___x_3164_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_cases_spec__2___boxed(
    mut v_sz_3166_: *mut leanh::LeanObject,
    mut v_i_3167_: *mut leanh::LeanObject,
    mut v_bs_3168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3169_: usize = 0;
    let mut v_i_boxed_3170_: usize = 0;
    let mut v_res_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3169_ = leanh::lean_unbox_usize(v_sz_3166_);
    leanh::lean_dec(v_sz_3166_);
    v_i_boxed_3170_ = leanh::lean_unbox_usize(v_i_3167_);
    leanh::lean_dec(v_i_3167_);
    v_res_3171_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_cases_spec__2(v_sz_boxed_3169_, v_i_boxed_3170_, v_bs_3168_);
    return v_res_3171_;
}
pub unsafe fn l_Lean_Meta_Grind_cases___lam__0(
    mut v_a_3177_: *mut leanh::LeanObject,
    mut v_a_3178_: *mut leanh::LeanObject,
    mut v_mvarId_3179_: *mut leanh::LeanObject,
    mut v_fvarId_3180_: *mut leanh::LeanObject,
    mut v_indices_3181_: *mut leanh::LeanObject,
    mut v___y_3182_: *mut leanh::LeanObject,
    mut v___y_3183_: *mut leanh::LeanObject,
    mut v___y_3184_: *mut leanh::LeanObject,
    mut v___y_3185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_3187_: usize = 0;
    let mut v___x_3188_: usize = 0;
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: u8 = 0;
    let mut v___x_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3216_: u8 = 0;
    let mut v_snd_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3223_: u8 = 0;
    let mut v_unused_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3228_: u8 = 0;
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3232_: u8 = 0;
    let mut v_a_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3236_: u8 = 0;
    let mut v___x_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3240_: u8 = 0;
    let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: u8 = 0;
    let mut v___x_3243_: u8 = 0;
    let mut v___x_3244_: usize = 0;
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: usize = 0;
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3251_: u8 = 0;
    let mut v___x_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3255_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_3187_ = lean_array_size(v_indices_3181_);
                v___x_3188_ = 0usize;
                leanh::lean_inc_ref(v_indices_3181_);
                v___x_3189_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Grind_cases_spec__2(v_sz_3187_, v___x_3188_, v_indices_3181_);
                v___x_3190_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg___closed__2;
                leanh::lean_inc_ref(v_a_3177_);
                leanh::lean_inc(v_fvarId_3180_);
                leanh::lean_inc(v_mvarId_3179_);
                v___x_3191_ = l_Lean_Meta_mkRecursorAppPrefix(
                    v_mvarId_3179_,
                    v___x_3190_,
                    v_fvarId_3180_,
                    v_a_3177_,
                    v___x_3189_,
                    v___y_3182_,
                    v___y_3183_,
                    v___y_3184_,
                    v___y_3185_,
                );
                if leanh::lean_obj_tag(v___x_3191_) == 0 {
                    v_a_3192_ = leanh::lean_ctor_get(v___x_3191_, 0);
                    leanh::lean_inc(v_a_3192_);
                    leanh::lean_dec_ref_known(v___x_3191_, 1);
                    v_lctx_3193_ = leanh::lean_ctor_get(v___y_3182_, 2);
                    v_localInstances_3194_ = leanh::lean_ctor_get(v___y_3182_, 3);
                    v___x_3195_ = 1;
                    leanh::lean_inc(v_fvarId_3180_);
                    leanh::lean_inc_ref(v_lctx_3193_);
                    v___x_3196_ =
                        l_Lean_LocalContext_setKind(v_lctx_3193_, v_fvarId_3180_, v___x_3195_);
                    v___x_3197_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3241_ = lean_array_get_size(v_indices_3181_);
                    v___x_3242_ = lean_nat_dec_lt(v___x_3197_, v___x_3241_);
                    if v___x_3242_ == 0 {
                        leanh::lean_dec_ref(v_indices_3181_);
                        v___y_3199_ = v___x_3196_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3243_ = lean_nat_dec_le(v___x_3241_, v___x_3241_);
                        if v___x_3243_ == 0 {
                            if v___x_3242_ == 0 {
                                leanh::lean_dec_ref(v_indices_3181_);
                                v___y_3199_ = v___x_3196_;
                                state = 1;
                                continue;
                            } else {
                                v___x_3244_ = lean_usize_of_nat(v___x_3241_);
                                v___x_3245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_cases_spec__4(v_indices_3181_, v___x_3188_, v___x_3244_, v___x_3196_);
                                leanh::lean_dec_ref(v_indices_3181_);
                                v___y_3199_ = v___x_3245_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_3246_ = lean_usize_of_nat(v___x_3241_);
                            v___x_3247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Grind_cases_spec__4(v_indices_3181_, v___x_3188_, v___x_3246_, v___x_3196_);
                            leanh::lean_dec_ref(v_indices_3181_);
                            v___y_3199_ = v___x_3247_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_3189_);
                    leanh::lean_dec_ref(v_indices_3181_);
                    leanh::lean_dec(v_fvarId_3180_);
                    leanh::lean_dec(v_mvarId_3179_);
                    leanh::lean_dec(v_a_3178_);
                    leanh::lean_dec_ref(v_a_3177_);
                    v_a_3248_ = leanh::lean_ctor_get(v___x_3191_, 0);
                    v_isSharedCheck_3255_ = (!leanh::lean_is_exclusive(v___x_3191_)) as u8;
                    if v_isSharedCheck_3255_ == 0 {
                        v___x_3250_ = v___x_3191_;
                        v_isShared_3251_ = v_isSharedCheck_3255_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3248_);
                        leanh::lean_dec(v___x_3191_);
                        v___x_3250_ = leanh::lean_box(0);
                        v_isShared_3251_ = v_isSharedCheck_3255_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3200_ = l_Lean_mkAppN(v_a_3192_, v___x_3189_);
                leanh::lean_dec_ref(v___x_3189_);
                v___x_3201_ = l_Lean_mkFVar(v_fvarId_3180_);
                v___x_3202_ = l_Lean_Expr_app___override(v___x_3200_, v___x_3201_);
                leanh::lean_inc(v___y_3185_);
                leanh::lean_inc_ref(v___y_3184_);
                leanh::lean_inc(v___y_3183_);
                leanh::lean_inc_ref(v___y_3182_);
                leanh::lean_inc_ref(v___x_3202_);
                v___x_3203_ = lean_infer_type(
                    v___x_3202_,
                    v___y_3182_,
                    v___y_3183_,
                    v___y_3184_,
                    v___y_3185_,
                );
                if leanh::lean_obj_tag(v___x_3203_) == 0 {
                    v_a_3204_ = leanh::lean_ctor_get(v___x_3203_, 0);
                    leanh::lean_inc(v_a_3204_);
                    leanh::lean_dec_ref_known(v___x_3203_, 1);
                    v___x_3205_ = l_Lean_Meta_RecursorInfo_numMinors(v_a_3177_);
                    leanh::lean_dec_ref(v_a_3177_);
                    v___x_3206_ = l_Lean_Meta_Grind_cases___lam__0___closed__1;
                    v___x_3207_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3207_, 0, v_a_3204_);
                    leanh::lean_ctor_set(v___x_3207_, 1, v___x_3206_);
                    v___x_3208_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3208_, 0, v___x_3202_);
                    leanh::lean_ctor_set(v___x_3208_, 1, v___x_3207_);
                    leanh::lean_inc(v_mvarId_3179_);
                    leanh::lean_inc_ref(v_localInstances_3194_);
                    v___x_3209_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg(v___x_3205_, v___y_3199_, v_localInstances_3194_, v___x_3205_, v_a_3178_, v_mvarId_3179_, v___x_3197_, v___x_3208_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
                    leanh::lean_dec(v___x_3205_);
                    if leanh::lean_obj_tag(v___x_3209_) == 0 {
                        v_a_3210_ = leanh::lean_ctor_get(v___x_3209_, 0);
                        leanh::lean_inc(v_a_3210_);
                        leanh::lean_dec_ref_known(v___x_3209_, 1);
                        v_fst_3211_ = leanh::lean_ctor_get(v_a_3210_, 0);
                        leanh::lean_inc(v_fst_3211_);
                        v_snd_3212_ = leanh::lean_ctor_get(v_a_3210_, 1);
                        leanh::lean_inc(v_snd_3212_);
                        leanh::lean_dec(v_a_3210_);
                        v___x_3213_ =
                            l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg(
                                v_mvarId_3179_,
                                v_fst_3211_,
                                v___y_3183_,
                            );
                        v_isSharedCheck_3223_ =
                            (!leanh::lean_is_exclusive(v___x_3213_)) as u8;
                        if v_isSharedCheck_3223_ == 0 {
                            v_unused_3224_ = leanh::lean_ctor_get(v___x_3213_, 0);
                            leanh::lean_dec(v_unused_3224_);
                            v___x_3215_ = v___x_3213_;
                            v_isShared_3216_ = v_isSharedCheck_3223_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_3213_);
                            v___x_3215_ = leanh::lean_box(0);
                            v_isShared_3216_ = v_isSharedCheck_3223_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_mvarId_3179_);
                        v_a_3225_ = leanh::lean_ctor_get(v___x_3209_, 0);
                        v_isSharedCheck_3232_ =
                            (!leanh::lean_is_exclusive(v___x_3209_)) as u8;
                        if v_isSharedCheck_3232_ == 0 {
                            v___x_3227_ = v___x_3209_;
                            v_isShared_3228_ = v_isSharedCheck_3232_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3225_);
                            leanh::lean_dec(v___x_3209_);
                            v___x_3227_ = leanh::lean_box(0);
                            v_isShared_3228_ = v_isSharedCheck_3232_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_3202_);
                    leanh::lean_dec_ref(v___y_3199_);
                    leanh::lean_dec(v_mvarId_3179_);
                    leanh::lean_dec(v_a_3178_);
                    leanh::lean_dec_ref(v_a_3177_);
                    v_a_3233_ = leanh::lean_ctor_get(v___x_3203_, 0);
                    v_isSharedCheck_3240_ = (!leanh::lean_is_exclusive(v___x_3203_)) as u8;
                    if v_isSharedCheck_3240_ == 0 {
                        v___x_3235_ = v___x_3203_;
                        v_isShared_3236_ = v_isSharedCheck_3240_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3233_);
                        leanh::lean_dec(v___x_3203_);
                        v___x_3235_ = leanh::lean_box(0);
                        v_isShared_3236_ = v_isSharedCheck_3240_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_3217_ = leanh::lean_ctor_get(v_snd_3212_, 1);
                leanh::lean_inc(v_snd_3217_);
                leanh::lean_dec(v_snd_3212_);
                v_fst_3218_ = leanh::lean_ctor_get(v_snd_3217_, 0);
                leanh::lean_inc(v_fst_3218_);
                leanh::lean_dec(v_snd_3217_);
                v___x_3219_ = lean_array_to_list(v_fst_3218_);
                if v_isShared_3216_ == 0 {
                    leanh::lean_ctor_set(v___x_3215_, 0, v___x_3219_);
                    v___x_3221_ = v___x_3215_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3222_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3222_, 0, v___x_3219_);
                    v___x_3221_ = v_reuseFailAlloc_3222_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3221_;
            }
            4 => {
                if v_isShared_3228_ == 0 {
                    v___x_3230_ = v___x_3227_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3231_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_a_3225_);
                    v___x_3230_ = v_reuseFailAlloc_3231_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3230_;
            }
            6 => {
                if v_isShared_3236_ == 0 {
                    v___x_3238_ = v___x_3235_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3239_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_a_3233_);
                    v___x_3238_ = v_reuseFailAlloc_3239_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3238_;
            }
            8 => {
                if v_isShared_3251_ == 0 {
                    v___x_3253_ = v___x_3250_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3254_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
                    v___x_3253_ = v_reuseFailAlloc_3254_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3253_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_cases___lam__0___boxed(
    mut v_a_3256_: *mut leanh::LeanObject,
    mut v_a_3257_: *mut leanh::LeanObject,
    mut v_mvarId_3258_: *mut leanh::LeanObject,
    mut v_fvarId_3259_: *mut leanh::LeanObject,
    mut v_indices_3260_: *mut leanh::LeanObject,
    mut v___y_3261_: *mut leanh::LeanObject,
    mut v___y_3262_: *mut leanh::LeanObject,
    mut v___y_3263_: *mut leanh::LeanObject,
    mut v___y_3264_: *mut leanh::LeanObject,
    mut v___y_3265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3266_ = l_Lean_Meta_Grind_cases___lam__0(
        v_a_3256_,
        v_a_3257_,
        v_mvarId_3258_,
        v_fvarId_3259_,
        v_indices_3260_,
        v___y_3261_,
        v___y_3262_,
        v___y_3263_,
        v___y_3264_,
    );
    leanh::lean_dec(v___y_3264_);
    leanh::lean_dec_ref(v___y_3263_);
    leanh::lean_dec(v___y_3262_);
    leanh::lean_dec_ref(v___y_3261_);
    return v_res_3266_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3268_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__0;
    v___x_3269_ = l_Lean_stringToMessageData(v___x_3268_);
    return v___x_3269_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3271_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__2;
    v___x_3272_ = l_Lean_stringToMessageData(v___x_3271_);
    return v___x_3272_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3274_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__4;
    v___x_3275_ = l_Lean_stringToMessageData(v___x_3274_);
    return v___x_3275_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3277_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__6;
    v___x_3278_ = l_Lean_stringToMessageData(v___x_3277_);
    return v___x_3278_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3280_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__8;
    v___x_3281_ = l_Lean_stringToMessageData(v___x_3280_);
    return v___x_3281_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3283_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__10;
    v___x_3284_ = l_Lean_stringToMessageData(v___x_3283_);
    return v___x_3284_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3286_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__12;
    v___x_3287_ = l_Lean_stringToMessageData(v___x_3286_);
    return v___x_3287_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg(
    mut v_msg_3288_: *mut leanh::LeanObject,
    mut v_declHint_3289_: *mut leanh::LeanObject,
    mut v___y_3290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: u8 = 0;
    let mut v_isExporting_3295_: u8 = 0;
    let mut v___x_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: u8 = 0;
    let mut v___x_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3317_: u8 = 0;
    let mut v___x_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: u8 = 0;
    let mut v___x_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3349_: u8 = 0;
    let mut v___x_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3292_ = lean_st_ref_get(v___y_3290_);
                v_env_3293_ = leanh::lean_ctor_get(v___x_3292_, 0);
                leanh::lean_inc_ref(v_env_3293_);
                leanh::lean_dec(v___x_3292_);
                v___x_3294_ = l_Lean_Name_isAnonymous(v_declHint_3289_);
                if v___x_3294_ == 0 {
                    v_isExporting_3295_ = leanh::lean_ctor_get_uint8(
                        v_env_3293_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_3295_ == 0 {
                        leanh::lean_dec_ref(v_env_3293_);
                        leanh::lean_dec(v_declHint_3289_);
                        v___x_3296_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3296_, 0, v_msg_3288_);
                        return v___x_3296_;
                    } else {
                        leanh::lean_inc_ref(v_env_3293_);
                        v___x_3297_ = l_Lean_Environment_setExporting(v_env_3293_, v___x_3294_);
                        leanh::lean_inc(v_declHint_3289_);
                        leanh::lean_inc_ref(v___x_3297_);
                        v___x_3298_ = l_Lean_Environment_contains(
                            v___x_3297_,
                            v_declHint_3289_,
                            v_isExporting_3295_,
                        );
                        if v___x_3298_ == 0 {
                            leanh::lean_dec_ref(v___x_3297_);
                            leanh::lean_dec_ref(v_env_3293_);
                            leanh::lean_dec(v_declHint_3289_);
                            v___x_3299_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3299_, 0, v_msg_3288_);
                            return v___x_3299_;
                        } else {
                            v___x_3300_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__2);
                            v___x_3301_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_validateCasesAttr_spec__0_spec__0___closed__5);
                            v___x_3302_ = l_Lean_Options_empty;
                            v___x_3303_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_3303_, 0, v___x_3297_);
                            leanh::lean_ctor_set(v___x_3303_, 1, v___x_3300_);
                            leanh::lean_ctor_set(v___x_3303_, 2, v___x_3301_);
                            leanh::lean_ctor_set(v___x_3303_, 3, v___x_3302_);
                            leanh::lean_inc(v_declHint_3289_);
                            v___x_3304_ =
                                l_Lean_MessageData_ofConstName(v_declHint_3289_, v___x_3294_);
                            v_c_3305_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_3305_, 0, v___x_3303_);
                            leanh::lean_ctor_set(v_c_3305_, 1, v___x_3304_);
                            v___x_3306_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_3293_,
                                v_declHint_3289_,
                            );
                            if leanh::lean_obj_tag(v___x_3306_) == 0 {
                                leanh::lean_dec_ref(v_env_3293_);
                                leanh::lean_dec(v_declHint_3289_);
                                v___x_3307_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1);
                                v___x_3308_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3308_, 0, v___x_3307_);
                                leanh::lean_ctor_set(v___x_3308_, 1, v_c_3305_);
                                v___x_3309_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__3);
                                v___x_3310_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3310_, 0, v___x_3308_);
                                leanh::lean_ctor_set(v___x_3310_, 1, v___x_3309_);
                                v___x_3311_ = l_Lean_MessageData_note(v___x_3310_);
                                v___x_3312_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3312_, 0, v_msg_3288_);
                                leanh::lean_ctor_set(v___x_3312_, 1, v___x_3311_);
                                v___x_3313_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3313_, 0, v___x_3312_);
                                return v___x_3313_;
                            } else {
                                v_val_3314_ = leanh::lean_ctor_get(v___x_3306_, 0);
                                v_isSharedCheck_3349_ =
                                    (!leanh::lean_is_exclusive(v___x_3306_)) as u8;
                                if v_isSharedCheck_3349_ == 0 {
                                    v___x_3316_ = v___x_3306_;
                                    v_isShared_3317_ = v_isSharedCheck_3349_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_3314_);
                                    leanh::lean_dec(v___x_3306_);
                                    v___x_3316_ = leanh::lean_box(0);
                                    v_isShared_3317_ = v_isSharedCheck_3349_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_3293_);
                    leanh::lean_dec(v_declHint_3289_);
                    v___x_3350_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3350_, 0, v_msg_3288_);
                    return v___x_3350_;
                }
            }
            1 => {
                v___x_3318_ = leanh::lean_box(0);
                v___x_3319_ = l_Lean_Environment_header(v_env_3293_);
                leanh::lean_dec_ref(v_env_3293_);
                v___x_3320_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3319_);
                v_mod_3321_ = lean_array_get(v___x_3318_, v___x_3320_, v_val_3314_);
                leanh::lean_dec(v_val_3314_);
                leanh::lean_dec_ref(v___x_3320_);
                v___x_3322_ = l_Lean_isPrivateName(v_declHint_3289_);
                leanh::lean_dec(v_declHint_3289_);
                if v___x_3322_ == 0 {
                    v___x_3323_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__5);
                    v___x_3324_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3324_, 0, v___x_3323_);
                    leanh::lean_ctor_set(v___x_3324_, 1, v_c_3305_);
                    v___x_3325_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__7);
                    v___x_3326_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3326_, 0, v___x_3324_);
                    leanh::lean_ctor_set(v___x_3326_, 1, v___x_3325_);
                    v___x_3327_ = l_Lean_MessageData_ofName(v_mod_3321_);
                    v___x_3328_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3328_, 0, v___x_3326_);
                    leanh::lean_ctor_set(v___x_3328_, 1, v___x_3327_);
                    v___x_3329_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__9);
                    v___x_3330_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3330_, 0, v___x_3328_);
                    leanh::lean_ctor_set(v___x_3330_, 1, v___x_3329_);
                    v___x_3331_ = l_Lean_MessageData_note(v___x_3330_);
                    v___x_3332_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3332_, 0, v_msg_3288_);
                    leanh::lean_ctor_set(v___x_3332_, 1, v___x_3331_);
                    if v_isShared_3317_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3316_, 0);
                        leanh::lean_ctor_set(v___x_3316_, 0, v___x_3332_);
                        v___x_3334_ = v___x_3316_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3335_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3335_, 0, v___x_3332_);
                        v___x_3334_ = v_reuseFailAlloc_3335_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3336_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__1);
                    v___x_3337_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3337_, 0, v___x_3336_);
                    leanh::lean_ctor_set(v___x_3337_, 1, v_c_3305_);
                    v___x_3338_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__11);
                    v___x_3339_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3339_, 0, v___x_3337_);
                    leanh::lean_ctor_set(v___x_3339_, 1, v___x_3338_);
                    v___x_3340_ = l_Lean_MessageData_ofName(v_mod_3321_);
                    v___x_3341_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3341_, 0, v___x_3339_);
                    leanh::lean_ctor_set(v___x_3341_, 1, v___x_3340_);
                    v___x_3342_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___closed__13);
                    v___x_3343_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3343_, 0, v___x_3341_);
                    leanh::lean_ctor_set(v___x_3343_, 1, v___x_3342_);
                    v___x_3344_ = l_Lean_MessageData_note(v___x_3343_);
                    v___x_3345_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3345_, 0, v_msg_3288_);
                    leanh::lean_ctor_set(v___x_3345_, 1, v___x_3344_);
                    if v_isShared_3317_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3316_, 0);
                        leanh::lean_ctor_set(v___x_3316_, 0, v___x_3345_);
                        v___x_3347_ = v___x_3316_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3348_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3348_, 0, v___x_3345_);
                        v___x_3347_ = v_reuseFailAlloc_3348_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3334_;
            }
            3 => {
                return v___x_3347_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg___boxed(
    mut v_msg_3351_: *mut leanh::LeanObject,
    mut v_declHint_3352_: *mut leanh::LeanObject,
    mut v___y_3353_: *mut leanh::LeanObject,
    mut v___y_3354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3355_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg(v_msg_3351_, v_declHint_3352_, v___y_3353_);
    leanh::lean_dec(v___y_3353_);
    return v_res_3355_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9(
    mut v_msg_3356_: *mut leanh::LeanObject,
    mut v_declHint_3357_: *mut leanh::LeanObject,
    mut v___y_3358_: *mut leanh::LeanObject,
    mut v___y_3359_: *mut leanh::LeanObject,
    mut v___y_3360_: *mut leanh::LeanObject,
    mut v___y_3361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3367_: u8 = 0;
    let mut v___x_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3373_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3363_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg(v_msg_3356_, v_declHint_3357_, v___y_3361_);
                v_a_3364_ = leanh::lean_ctor_get(v___x_3363_, 0);
                v_isSharedCheck_3373_ = (!leanh::lean_is_exclusive(v___x_3363_)) as u8;
                if v_isSharedCheck_3373_ == 0 {
                    v___x_3366_ = v___x_3363_;
                    v_isShared_3367_ = v_isSharedCheck_3373_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3364_);
                    leanh::lean_dec(v___x_3363_);
                    v___x_3366_ = leanh::lean_box(0);
                    v_isShared_3367_ = v_isSharedCheck_3373_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3368_ = l_Lean_unknownIdentifierMessageTag;
                v___x_3369_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3369_, 0, v___x_3368_);
                leanh::lean_ctor_set(v___x_3369_, 1, v_a_3364_);
                if v_isShared_3367_ == 0 {
                    leanh::lean_ctor_set(v___x_3366_, 0, v___x_3369_);
                    v___x_3371_ = v___x_3366_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3372_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3369_);
                    v___x_3371_ = v_reuseFailAlloc_3372_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3371_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9___boxed(
    mut v_msg_3374_: *mut leanh::LeanObject,
    mut v_declHint_3375_: *mut leanh::LeanObject,
    mut v___y_3376_: *mut leanh::LeanObject,
    mut v___y_3377_: *mut leanh::LeanObject,
    mut v___y_3378_: *mut leanh::LeanObject,
    mut v___y_3379_: *mut leanh::LeanObject,
    mut v___y_3380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3381_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9(v_msg_3374_, v_declHint_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
    leanh::lean_dec(v___y_3379_);
    leanh::lean_dec_ref(v___y_3378_);
    leanh::lean_dec(v___y_3377_);
    leanh::lean_dec_ref(v___y_3376_);
    return v_res_3381_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__16(
    mut v_msgData_3382_: *mut leanh::LeanObject,
    mut v___y_3383_: *mut leanh::LeanObject,
    mut v___y_3384_: *mut leanh::LeanObject,
    mut v___y_3385_: *mut leanh::LeanObject,
    mut v___y_3386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3388_ = lean_st_ref_get(v___y_3386_);
    v_env_3389_ = leanh::lean_ctor_get(v___x_3388_, 0);
    leanh::lean_inc_ref(v_env_3389_);
    leanh::lean_dec(v___x_3388_);
    v___x_3390_ = lean_st_ref_get(v___y_3384_);
    v_mctx_3391_ = leanh::lean_ctor_get(v___x_3390_, 0);
    leanh::lean_inc_ref(v_mctx_3391_);
    leanh::lean_dec(v___x_3390_);
    v_lctx_3392_ = leanh::lean_ctor_get(v___y_3383_, 2);
    v_options_3393_ = leanh::lean_ctor_get(v___y_3385_, 2);
    leanh::lean_inc_ref(v_options_3393_);
    leanh::lean_inc_ref(v_lctx_3392_);
    v___x_3394_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3394_, 0, v_env_3389_);
    leanh::lean_ctor_set(v___x_3394_, 1, v_mctx_3391_);
    leanh::lean_ctor_set(v___x_3394_, 2, v_lctx_3392_);
    leanh::lean_ctor_set(v___x_3394_, 3, v_options_3393_);
    v___x_3395_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3395_, 0, v___x_3394_);
    leanh::lean_ctor_set(v___x_3395_, 1, v_msgData_3382_);
    v___x_3396_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3396_, 0, v___x_3395_);
    return v___x_3396_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__16___boxed(
    mut v_msgData_3397_: *mut leanh::LeanObject,
    mut v___y_3398_: *mut leanh::LeanObject,
    mut v___y_3399_: *mut leanh::LeanObject,
    mut v___y_3400_: *mut leanh::LeanObject,
    mut v___y_3401_: *mut leanh::LeanObject,
    mut v___y_3402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3403_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__16(v_msgData_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
    leanh::lean_dec(v___y_3401_);
    leanh::lean_dec_ref(v___y_3400_);
    leanh::lean_dec(v___y_3399_);
    leanh::lean_dec_ref(v___y_3398_);
    return v_res_3403_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(
    mut v_msg_3404_: *mut leanh::LeanObject,
    mut v___y_3405_: *mut leanh::LeanObject,
    mut v___y_3406_: *mut leanh::LeanObject,
    mut v___y_3407_: *mut leanh::LeanObject,
    mut v___y_3408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3415_: u8 = 0;
    let mut v___x_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3420_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3410_ = leanh::lean_ctor_get(v___y_3407_, 5);
                v___x_3411_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__16(v_msg_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_);
                v_a_3412_ = leanh::lean_ctor_get(v___x_3411_, 0);
                v_isSharedCheck_3420_ = (!leanh::lean_is_exclusive(v___x_3411_)) as u8;
                if v_isSharedCheck_3420_ == 0 {
                    v___x_3414_ = v___x_3411_;
                    v_isShared_3415_ = v_isSharedCheck_3420_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3412_);
                    leanh::lean_dec(v___x_3411_);
                    v___x_3414_ = leanh::lean_box(0);
                    v_isShared_3415_ = v_isSharedCheck_3420_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_3410_);
                v___x_3416_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3416_, 0, v_ref_3410_);
                leanh::lean_ctor_set(v___x_3416_, 1, v_a_3412_);
                if v_isShared_3415_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3414_, 1);
                    leanh::lean_ctor_set(v___x_3414_, 0, v___x_3416_);
                    v___x_3418_ = v___x_3414_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3419_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___x_3416_);
                    v___x_3418_ = v_reuseFailAlloc_3419_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3418_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg___boxed(
    mut v_msg_3421_: *mut leanh::LeanObject,
    mut v___y_3422_: *mut leanh::LeanObject,
    mut v___y_3423_: *mut leanh::LeanObject,
    mut v___y_3424_: *mut leanh::LeanObject,
    mut v___y_3425_: *mut leanh::LeanObject,
    mut v___y_3426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3427_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(v_msg_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
    leanh::lean_dec(v___y_3425_);
    leanh::lean_dec_ref(v___y_3424_);
    leanh::lean_dec(v___y_3423_);
    leanh::lean_dec_ref(v___y_3422_);
    return v_res_3427_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(
    mut v_ref_3428_: *mut leanh::LeanObject,
    mut v_msg_3429_: *mut leanh::LeanObject,
    mut v___y_3430_: *mut leanh::LeanObject,
    mut v___y_3431_: *mut leanh::LeanObject,
    mut v___y_3432_: *mut leanh::LeanObject,
    mut v___y_3433_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3447_: u8 = 0;
    let mut v_cancelTk_x3f_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3449_: u8 = 0;
    let mut v_inheritedTraceOptions_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_3435_ = leanh::lean_ctor_get(v___y_3432_, 0);
    v_fileMap_3436_ = leanh::lean_ctor_get(v___y_3432_, 1);
    v_options_3437_ = leanh::lean_ctor_get(v___y_3432_, 2);
    v_currRecDepth_3438_ = leanh::lean_ctor_get(v___y_3432_, 3);
    v_maxRecDepth_3439_ = leanh::lean_ctor_get(v___y_3432_, 4);
    v_ref_3440_ = leanh::lean_ctor_get(v___y_3432_, 5);
    v_currNamespace_3441_ = leanh::lean_ctor_get(v___y_3432_, 6);
    v_openDecls_3442_ = leanh::lean_ctor_get(v___y_3432_, 7);
    v_initHeartbeats_3443_ = leanh::lean_ctor_get(v___y_3432_, 8);
    v_maxHeartbeats_3444_ = leanh::lean_ctor_get(v___y_3432_, 9);
    v_quotContext_3445_ = leanh::lean_ctor_get(v___y_3432_, 10);
    v_currMacroScope_3446_ = leanh::lean_ctor_get(v___y_3432_, 11);
    v_diag_3447_ = leanh::lean_ctor_get_uint8(
        v___y_3432_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3448_ = leanh::lean_ctor_get(v___y_3432_, 12);
    v_suppressElabErrors_3449_ = leanh::lean_ctor_get_uint8(
        v___y_3432_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3450_ = leanh::lean_ctor_get(v___y_3432_, 13);
    v_ref_3451_ = l_Lean_replaceRef(v_ref_3428_, v_ref_3440_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_3450_);
    leanh::lean_inc(v_cancelTk_x3f_3448_);
    leanh::lean_inc(v_currMacroScope_3446_);
    leanh::lean_inc(v_quotContext_3445_);
    leanh::lean_inc(v_maxHeartbeats_3444_);
    leanh::lean_inc(v_initHeartbeats_3443_);
    leanh::lean_inc(v_openDecls_3442_);
    leanh::lean_inc(v_currNamespace_3441_);
    leanh::lean_inc(v_maxRecDepth_3439_);
    leanh::lean_inc(v_currRecDepth_3438_);
    leanh::lean_inc_ref(v_options_3437_);
    leanh::lean_inc_ref(v_fileMap_3436_);
    leanh::lean_inc_ref(v_fileName_3435_);
    v___x_3452_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_3452_, 0, v_fileName_3435_);
    leanh::lean_ctor_set(v___x_3452_, 1, v_fileMap_3436_);
    leanh::lean_ctor_set(v___x_3452_, 2, v_options_3437_);
    leanh::lean_ctor_set(v___x_3452_, 3, v_currRecDepth_3438_);
    leanh::lean_ctor_set(v___x_3452_, 4, v_maxRecDepth_3439_);
    leanh::lean_ctor_set(v___x_3452_, 5, v_ref_3451_);
    leanh::lean_ctor_set(v___x_3452_, 6, v_currNamespace_3441_);
    leanh::lean_ctor_set(v___x_3452_, 7, v_openDecls_3442_);
    leanh::lean_ctor_set(v___x_3452_, 8, v_initHeartbeats_3443_);
    leanh::lean_ctor_set(v___x_3452_, 9, v_maxHeartbeats_3444_);
    leanh::lean_ctor_set(v___x_3452_, 10, v_quotContext_3445_);
    leanh::lean_ctor_set(v___x_3452_, 11, v_currMacroScope_3446_);
    leanh::lean_ctor_set(v___x_3452_, 12, v_cancelTk_x3f_3448_);
    leanh::lean_ctor_set(v___x_3452_, 13, v_inheritedTraceOptions_3450_);
    leanh::lean_ctor_set_uint8(
        v___x_3452_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_3447_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_3452_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3449_,
    );
    v___x_3453_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(v_msg_3429_, v___y_3430_, v___y_3431_, v___x_3452_, v___y_3433_);
    leanh::lean_dec_ref_known(v___x_3452_, 14);
    return v___x_3453_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg___boxed(
    mut v_ref_3454_: *mut leanh::LeanObject,
    mut v_msg_3455_: *mut leanh::LeanObject,
    mut v___y_3456_: *mut leanh::LeanObject,
    mut v___y_3457_: *mut leanh::LeanObject,
    mut v___y_3458_: *mut leanh::LeanObject,
    mut v___y_3459_: *mut leanh::LeanObject,
    mut v___y_3460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3461_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(v_ref_3454_, v_msg_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
    leanh::lean_dec(v___y_3459_);
    leanh::lean_dec_ref(v___y_3458_);
    leanh::lean_dec(v___y_3457_);
    leanh::lean_dec_ref(v___y_3456_);
    leanh::lean_dec(v_ref_3454_);
    return v_res_3461_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg(
    mut v_ref_3462_: *mut leanh::LeanObject,
    mut v_msg_3463_: *mut leanh::LeanObject,
    mut v_declHint_3464_: *mut leanh::LeanObject,
    mut v___y_3465_: *mut leanh::LeanObject,
    mut v___y_3466_: *mut leanh::LeanObject,
    mut v___y_3467_: *mut leanh::LeanObject,
    mut v___y_3468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3470_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9(v_msg_3463_, v_declHint_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
    v_a_3471_ = leanh::lean_ctor_get(v___x_3470_, 0);
    leanh::lean_inc(v_a_3471_);
    leanh::lean_dec_ref(v___x_3470_);
    v___x_3472_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(v_ref_3462_, v_a_3471_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
    return v___x_3472_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg___boxed(
    mut v_ref_3473_: *mut leanh::LeanObject,
    mut v_msg_3474_: *mut leanh::LeanObject,
    mut v_declHint_3475_: *mut leanh::LeanObject,
    mut v___y_3476_: *mut leanh::LeanObject,
    mut v___y_3477_: *mut leanh::LeanObject,
    mut v___y_3478_: *mut leanh::LeanObject,
    mut v___y_3479_: *mut leanh::LeanObject,
    mut v___y_3480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3481_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg(v_ref_3473_, v_msg_3474_, v_declHint_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
    leanh::lean_dec(v___y_3479_);
    leanh::lean_dec_ref(v___y_3478_);
    leanh::lean_dec(v___y_3477_);
    leanh::lean_dec_ref(v___y_3476_);
    leanh::lean_dec(v_ref_3473_);
    return v_res_3481_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3483_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__0;
    v___x_3484_ = l_Lean_stringToMessageData(v___x_3483_);
    return v___x_3484_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg(
    mut v_ref_3485_: *mut leanh::LeanObject,
    mut v_constName_3486_: *mut leanh::LeanObject,
    mut v___y_3487_: *mut leanh::LeanObject,
    mut v___y_3488_: *mut leanh::LeanObject,
    mut v___y_3489_: *mut leanh::LeanObject,
    mut v___y_3490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: u8 = 0;
    let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3492_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___closed__1);
    v___x_3493_ = 0;
    leanh::lean_inc(v_constName_3486_);
    v___x_3494_ = l_Lean_MessageData_ofConstName(v_constName_3486_, v___x_3493_);
    v___x_3495_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3495_, 0, v___x_3492_);
    leanh::lean_ctor_set(v___x_3495_, 1, v___x_3494_);
    v___x_3496_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1_once),
        _init_l_Lean_Meta_Grind_ensureNotBuiltinCases___closed__1,
    );
    v___x_3497_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3497_, 0, v___x_3495_);
    leanh::lean_ctor_set(v___x_3497_, 1, v___x_3496_);
    v___x_3498_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg(v_ref_3485_, v___x_3497_, v_constName_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
    return v___x_3498_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_ref_3499_: *mut leanh::LeanObject,
    mut v_constName_3500_: *mut leanh::LeanObject,
    mut v___y_3501_: *mut leanh::LeanObject,
    mut v___y_3502_: *mut leanh::LeanObject,
    mut v___y_3503_: *mut leanh::LeanObject,
    mut v___y_3504_: *mut leanh::LeanObject,
    mut v___y_3505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3506_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg(v_ref_3499_, v_constName_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
    leanh::lean_dec(v___y_3504_);
    leanh::lean_dec_ref(v___y_3503_);
    leanh::lean_dec(v___y_3502_);
    leanh::lean_dec_ref(v___y_3501_);
    leanh::lean_dec(v_ref_3499_);
    return v_res_3506_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg(
    mut v_constName_3507_: *mut leanh::LeanObject,
    mut v___y_3508_: *mut leanh::LeanObject,
    mut v___y_3509_: *mut leanh::LeanObject,
    mut v___y_3510_: *mut leanh::LeanObject,
    mut v___y_3511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_3513_ = leanh::lean_ctor_get(v___y_3510_, 5);
    v___x_3514_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg(v_ref_3513_, v_constName_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_);
    return v___x_3514_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg___boxed(
    mut v_constName_3515_: *mut leanh::LeanObject,
    mut v___y_3516_: *mut leanh::LeanObject,
    mut v___y_3517_: *mut leanh::LeanObject,
    mut v___y_3518_: *mut leanh::LeanObject,
    mut v___y_3519_: *mut leanh::LeanObject,
    mut v___y_3520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3521_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg(v_constName_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_);
    leanh::lean_dec(v___y_3519_);
    leanh::lean_dec_ref(v___y_3518_);
    leanh::lean_dec(v___y_3517_);
    leanh::lean_dec_ref(v___y_3516_);
    return v_res_3521_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0(
    mut v_constName_3522_: *mut leanh::LeanObject,
    mut v___y_3523_: *mut leanh::LeanObject,
    mut v___y_3524_: *mut leanh::LeanObject,
    mut v___y_3525_: *mut leanh::LeanObject,
    mut v___y_3526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: u8 = 0;
    let mut v___x_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3536_: u8 = 0;
    let mut v___x_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3540_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3528_ = lean_st_ref_get(v___y_3526_);
                v_env_3529_ = leanh::lean_ctor_get(v___x_3528_, 0);
                leanh::lean_inc_ref(v_env_3529_);
                leanh::lean_dec(v___x_3528_);
                v___x_3530_ = 0;
                leanh::lean_inc(v_constName_3522_);
                v___x_3531_ =
                    l_Lean_Environment_find_x3f(v_env_3529_, v_constName_3522_, v___x_3530_);
                if leanh::lean_obj_tag(v___x_3531_) == 0 {
                    v___x_3532_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg(v_constName_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_);
                    return v___x_3532_;
                } else {
                    leanh::lean_dec(v_constName_3522_);
                    v_val_3533_ = leanh::lean_ctor_get(v___x_3531_, 0);
                    v_isSharedCheck_3540_ = (!leanh::lean_is_exclusive(v___x_3531_)) as u8;
                    if v_isSharedCheck_3540_ == 0 {
                        v___x_3535_ = v___x_3531_;
                        v_isShared_3536_ = v_isSharedCheck_3540_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3533_);
                        leanh::lean_dec(v___x_3531_);
                        v___x_3535_ = leanh::lean_box(0);
                        v_isShared_3536_ = v_isSharedCheck_3540_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3536_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3535_, 0);
                    v___x_3538_ = v___x_3535_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3539_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_val_3533_);
                    v___x_3538_ = v_reuseFailAlloc_3539_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3538_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0___boxed(
    mut v_constName_3541_: *mut leanh::LeanObject,
    mut v___y_3542_: *mut leanh::LeanObject,
    mut v___y_3543_: *mut leanh::LeanObject,
    mut v___y_3544_: *mut leanh::LeanObject,
    mut v___y_3545_: *mut leanh::LeanObject,
    mut v___y_3546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3547_ = l_Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0(
        v_constName_3541_,
        v___y_3542_,
        v___y_3543_,
        v___y_3544_,
        v___y_3545_,
    );
    leanh::lean_dec(v___y_3545_);
    leanh::lean_dec_ref(v___y_3544_);
    leanh::lean_dec(v___y_3543_);
    leanh::lean_dec_ref(v___y_3542_);
    return v_res_3547_;
}
pub unsafe fn l_Lean_Meta_Grind_cases___lam__1(
    mut v_mvarId_3554_: *mut leanh::LeanObject,
    mut v_e_3555_: *mut leanh::LeanObject,
    mut v___y_3556_: *mut leanh::LeanObject,
    mut v___y_3557_: *mut leanh::LeanObject,
    mut v___y_3558_: *mut leanh::LeanObject,
    mut v___y_3559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: u8 = 0;
    let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: u8 = 0;
    let mut v___x_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3597_: u8 = 0;
    let mut v___x_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3601_: u8 = 0;
    let mut v___x_3602_: u8 = 0;
    let mut v___x_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: u8 = 0;
    let mut v___x_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3636_: u8 = 0;
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3640_: u8 = 0;
    let mut v_a_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3644_: u8 = 0;
    let mut v___x_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3648_: u8 = 0;
    let mut v_a_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3652_: u8 = 0;
    let mut v___x_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3656_: u8 = 0;
    let mut v___x_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3663_: u8 = 0;
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3667_: u8 = 0;
    let mut v___x_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indicesFVarIds_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3678_: u8 = 0;
    let mut v___x_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3682_: u8 = 0;
    let mut v_a_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3686_: u8 = 0;
    let mut v___x_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3690_: u8 = 0;
    let mut v___x_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3695_: u8 = 0;
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3699_: u8 = 0;
    let mut v___x_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3704_: u8 = 0;
    let mut v___x_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3708_: u8 = 0;
    let mut v_a_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3712_: u8 = 0;
    let mut v___x_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3716_: u8 = 0;
    let mut v_a_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3720_: u8 = 0;
    let mut v___x_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3724_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvarId_3554_);
                v___x_3561_ = l_Lean_MVarId_getTag(
                    v_mvarId_3554_,
                    v___y_3556_,
                    v___y_3557_,
                    v___y_3558_,
                    v___y_3559_,
                );
                if leanh::lean_obj_tag(v___x_3561_) == 0 {
                    v_a_3562_ = leanh::lean_ctor_get(v___x_3561_, 0);
                    leanh::lean_inc(v_a_3562_);
                    leanh::lean_dec_ref_known(v___x_3561_, 1);
                    leanh::lean_inc(v___y_3559_);
                    leanh::lean_inc_ref(v___y_3558_);
                    leanh::lean_inc(v___y_3557_);
                    leanh::lean_inc_ref(v___y_3556_);
                    leanh::lean_inc_ref(v_e_3555_);
                    v___x_3563_ = lean_infer_type(
                        v_e_3555_,
                        v___y_3556_,
                        v___y_3557_,
                        v___y_3558_,
                        v___y_3559_,
                    );
                    if leanh::lean_obj_tag(v___x_3563_) == 0 {
                        v_a_3564_ = leanh::lean_ctor_get(v___x_3563_, 0);
                        leanh::lean_inc(v_a_3564_);
                        leanh::lean_dec_ref_known(v___x_3563_, 1);
                        leanh::lean_inc(v___y_3559_);
                        leanh::lean_inc_ref(v___y_3558_);
                        leanh::lean_inc(v___y_3557_);
                        leanh::lean_inc_ref(v___y_3556_);
                        v___x_3565_ = lean_whnf(
                            v_a_3564_,
                            v___y_3556_,
                            v___y_3557_,
                            v___y_3558_,
                            v___y_3559_,
                        );
                        if leanh::lean_obj_tag(v___x_3565_) == 0 {
                            v_a_3566_ = leanh::lean_ctor_get(v___x_3565_, 0);
                            leanh::lean_inc(v_a_3566_);
                            leanh::lean_dec_ref_known(v___x_3565_, 1);
                            v___x_3567_ = l_Lean_Expr_getAppFn(v_a_3566_);
                            if leanh::lean_obj_tag(v___x_3567_) == 4 {
                                v_declName_3568_ = leanh::lean_ctor_get(v___x_3567_, 0);
                                leanh::lean_inc_n(v_declName_3568_, 2);
                                leanh::lean_dec_ref_known(v___x_3567_, 2);
                                v___x_3569_ =
                                    l_Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0(
                                        v_declName_3568_,
                                        v___y_3556_,
                                        v___y_3557_,
                                        v___y_3558_,
                                        v___y_3559_,
                                    );
                                if leanh::lean_obj_tag(v___x_3569_) == 0 {
                                    v_a_3570_ = leanh::lean_ctor_get(v___x_3569_, 0);
                                    leanh::lean_inc(v_a_3570_);
                                    leanh::lean_dec_ref_known(v___x_3569_, 1);
                                    if leanh::lean_obj_tag(v_a_3570_) == 5 {
                                        leanh::lean_dec_ref_known(v_a_3570_, 1);
                                        v___x_3571_ = l_Lean_mkCasesOnName(v_declName_3568_);
                                        v___x_3572_ = leanh::lean_box(0);
                                        v___x_3573_ = l_Lean_Meta_mkRecursorInfo(
                                            v___x_3571_,
                                            v___x_3572_,
                                            v___y_3556_,
                                            v___y_3557_,
                                            v___y_3558_,
                                            v___y_3559_,
                                        );
                                        if leanh::lean_obj_tag(v___x_3573_) == 0 {
                                            v_a_3574_ = leanh::lean_ctor_get(v___x_3573_, 0);
                                            leanh::lean_inc(v_a_3574_);
                                            leanh::lean_dec_ref_known(v___x_3573_, 1);
                                            v___x_3575_ = leanh::lean_unsigned_to_nat(0);
                                            v___x_3576_ =
                                                l_Lean_Meta_RecursorInfo_numIndices(v_a_3574_);
                                            v___x_3577_ = lean_nat_dec_lt(v___x_3575_, v___x_3576_);
                                            leanh::lean_dec(v___x_3576_);
                                            if v___x_3577_ == 0 {
                                                leanh::lean_inc_ref(v_e_3555_);
                                                v___x_3578_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_isSimpleFVar(v_e_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_);
                                                if leanh::lean_obj_tag(v___x_3578_) == 0 {
                                                    v_a_3579_ =
                                                        leanh::lean_ctor_get(v___x_3578_, 0);
                                                    leanh::lean_inc(v_a_3579_);
                                                    leanh::lean_dec_ref_known(
                                                        v___x_3578_,
                                                        1,
                                                    );
                                                    v___x_3602_ =
                                                        (leanh::lean_unbox(v_a_3579_) as u8);
                                                    if v___x_3602_ == 0 {
                                                        leanh::lean_inc_ref(v_e_3555_);
                                                        v___x_3603_ = l_Lean_Meta_isProof(
                                                            v_e_3555_,
                                                            v___y_3556_,
                                                            v___y_3557_,
                                                            v___y_3558_,
                                                            v___y_3559_,
                                                        );
                                                        if leanh::lean_obj_tag(v___x_3603_)
                                                            == 0
                                                        {
                                                            v_a_3604_ = leanh::lean_ctor_get(
                                                                v___x_3603_,
                                                                0,
                                                            );
                                                            leanh::lean_inc(v_a_3604_);
                                                            leanh::lean_dec_ref_known(
                                                                v___x_3603_,
                                                                1,
                                                            );
                                                            v___x_3605_ = (leanh::lean_unbox(
                                                                v_a_3604_,
                                                            )
                                                                as u8);
                                                            leanh::lean_dec(v_a_3604_);
                                                            if v___x_3605_ == 0 {
                                                                v___x_3606_ = l_Lean_Meta_Grind_cases___lam__1___closed__1;
                                                                v___x_3607_ =
                                                                    l_Lean_Core_mkFreshUserName(
                                                                        v___x_3606_,
                                                                        v___y_3558_,
                                                                        v___y_3559_,
                                                                    );
                                                                if leanh::lean_obj_tag(
                                                                    v___x_3607_,
                                                                ) == 0
                                                                {
                                                                    v_a_3608_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_3607_,
                                                                            0,
                                                                        );
                                                                    leanh::lean_inc(
                                                                        v_a_3608_,
                                                                    );
                                                                    leanh::lean_dec_ref_known(v___x_3607_, 1);
                                                                    v___x_3609_ = l_Lean_Meta_Grind_cases___lam__1___closed__3;
                                                                    v___x_3610_ =
                                                                        l_Lean_MVarId_assertExt(
                                                                            v_mvarId_3554_,
                                                                            v_a_3608_,
                                                                            v_a_3566_,
                                                                            v_e_3555_,
                                                                            v___x_3609_,
                                                                            v___y_3556_,
                                                                            v___y_3557_,
                                                                            v___y_3558_,
                                                                            v___y_3559_,
                                                                        );
                                                                    if leanh::lean_obj_tag(
                                                                        v___x_3610_,
                                                                    ) == 0
                                                                    {
                                                                        v_a_3611_ = leanh::lean_ctor_get(v___x_3610_, 0);
                                                                        leanh::lean_inc(
                                                                            v_a_3611_,
                                                                        );
                                                                        leanh::lean_dec_ref_known(v___x_3610_, 1);
                                                                        v_mvarId_3581_ = v_a_3611_;
                                                                        v___y_3582_ = v___y_3556_;
                                                                        v___y_3583_ = v___y_3557_;
                                                                        v___y_3584_ = v___y_3558_;
                                                                        v___y_3585_ = v___y_3559_;
                                                                        state = 1;
                                                                        continue;
                                                                    } else {
                                                                        leanh::lean_dec(
                                                                            v_a_3579_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_a_3574_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_a_3562_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v___y_3559_,
                                                                        );
                                                                        leanh::lean_dec_ref(
                                                                            v___y_3558_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v___y_3557_,
                                                                        );
                                                                        leanh::lean_dec_ref(
                                                                            v___y_3556_,
                                                                        );
                                                                        v_a_3612_ = leanh::lean_ctor_get(v___x_3610_, 0);
                                                                        v_isSharedCheck_3619_ = (!leanh::lean_is_exclusive(v___x_3610_)) as u8;
                                                                        if v_isSharedCheck_3619_
                                                                            == 0
                                                                        {
                                                                            v___x_3614_ =
                                                                                v___x_3610_;
                                                                            v_isShared_3615_ = v_isSharedCheck_3619_;
                                                                            state = 4;
                                                                            continue;
                                                                        } else {
                                                                            leanh::lean_inc(
                                                                                v_a_3612_,
                                                                            );
                                                                            leanh::lean_dec(
                                                                                v___x_3610_,
                                                                            );
                                                                            v___x_3614_ = leanh::lean_box(0);
                                                                            v_isShared_3615_ = v_isSharedCheck_3619_;
                                                                            state = 4;
                                                                            continue;
                                                                        }
                                                                    }
                                                                } else {
                                                                    leanh::lean_dec(
                                                                        v_a_3579_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_3574_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_3566_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_3562_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v___y_3559_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v___y_3558_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v___y_3557_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v___y_3556_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_e_3555_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_mvarId_3554_,
                                                                    );
                                                                    v_a_3620_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_3607_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_3627_ = (!leanh::lean_is_exclusive(v___x_3607_)) as u8;
                                                                    if v_isSharedCheck_3627_ == 0 {
                                                                        v___x_3622_ = v___x_3607_;
                                                                        v_isShared_3623_ =
                                                                            v_isSharedCheck_3627_;
                                                                        state = 6;
                                                                        continue;
                                                                    } else {
                                                                        leanh::lean_inc(
                                                                            v_a_3620_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v___x_3607_,
                                                                        );
                                                                        v___x_3622_ =
                                                                            leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_3623_ =
                                                                            v_isSharedCheck_3627_;
                                                                        state = 6;
                                                                        continue;
                                                                    }
                                                                }
                                                            } else {
                                                                v___x_3628_ = l_Lean_Meta_Grind_cases___lam__1___closed__1;
                                                                v___x_3629_ =
                                                                    l_Lean_Core_mkFreshUserName(
                                                                        v___x_3628_,
                                                                        v___y_3558_,
                                                                        v___y_3559_,
                                                                    );
                                                                if leanh::lean_obj_tag(
                                                                    v___x_3629_,
                                                                ) == 0
                                                                {
                                                                    v_a_3630_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_3629_,
                                                                            0,
                                                                        );
                                                                    leanh::lean_inc(
                                                                        v_a_3630_,
                                                                    );
                                                                    leanh::lean_dec_ref_known(v___x_3629_, 1);
                                                                    v___x_3631_ =
                                                                        l_Lean_MVarId_assert(
                                                                            v_mvarId_3554_,
                                                                            v_a_3630_,
                                                                            v_a_3566_,
                                                                            v_e_3555_,
                                                                            v___y_3556_,
                                                                            v___y_3557_,
                                                                            v___y_3558_,
                                                                            v___y_3559_,
                                                                        );
                                                                    if leanh::lean_obj_tag(
                                                                        v___x_3631_,
                                                                    ) == 0
                                                                    {
                                                                        v_a_3632_ = leanh::lean_ctor_get(v___x_3631_, 0);
                                                                        leanh::lean_inc(
                                                                            v_a_3632_,
                                                                        );
                                                                        leanh::lean_dec_ref_known(v___x_3631_, 1);
                                                                        v_mvarId_3581_ = v_a_3632_;
                                                                        v___y_3582_ = v___y_3556_;
                                                                        v___y_3583_ = v___y_3557_;
                                                                        v___y_3584_ = v___y_3558_;
                                                                        v___y_3585_ = v___y_3559_;
                                                                        state = 1;
                                                                        continue;
                                                                    } else {
                                                                        leanh::lean_dec(
                                                                            v_a_3579_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_a_3574_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v_a_3562_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v___y_3559_,
                                                                        );
                                                                        leanh::lean_dec_ref(
                                                                            v___y_3558_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v___y_3557_,
                                                                        );
                                                                        leanh::lean_dec_ref(
                                                                            v___y_3556_,
                                                                        );
                                                                        v_a_3633_ = leanh::lean_ctor_get(v___x_3631_, 0);
                                                                        v_isSharedCheck_3640_ = (!leanh::lean_is_exclusive(v___x_3631_)) as u8;
                                                                        if v_isSharedCheck_3640_
                                                                            == 0
                                                                        {
                                                                            v___x_3635_ =
                                                                                v___x_3631_;
                                                                            v_isShared_3636_ = v_isSharedCheck_3640_;
                                                                            state = 8;
                                                                            continue;
                                                                        } else {
                                                                            leanh::lean_inc(
                                                                                v_a_3633_,
                                                                            );
                                                                            leanh::lean_dec(
                                                                                v___x_3631_,
                                                                            );
                                                                            v___x_3635_ = leanh::lean_box(0);
                                                                            v_isShared_3636_ = v_isSharedCheck_3640_;
                                                                            state = 8;
                                                                            continue;
                                                                        }
                                                                    }
                                                                } else {
                                                                    leanh::lean_dec(
                                                                        v_a_3579_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_3574_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_3566_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_a_3562_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v___y_3559_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v___y_3558_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v___y_3557_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v___y_3556_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_e_3555_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_mvarId_3554_,
                                                                    );
                                                                    v_a_3641_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_3629_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_3648_ = (!leanh::lean_is_exclusive(v___x_3629_)) as u8;
                                                                    if v_isSharedCheck_3648_ == 0 {
                                                                        v___x_3643_ = v___x_3629_;
                                                                        v_isShared_3644_ =
                                                                            v_isSharedCheck_3648_;
                                                                        state = 10;
                                                                        continue;
                                                                    } else {
                                                                        leanh::lean_inc(
                                                                            v_a_3641_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v___x_3629_,
                                                                        );
                                                                        v___x_3643_ =
                                                                            leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_3644_ =
                                                                            v_isSharedCheck_3648_;
                                                                        state = 10;
                                                                        continue;
                                                                    }
                                                                }
                                                            }
                                                        } else {
                                                            leanh::lean_dec(v_a_3579_);
                                                            leanh::lean_dec(v_a_3574_);
                                                            leanh::lean_dec(v_a_3566_);
                                                            leanh::lean_dec(v_a_3562_);
                                                            leanh::lean_dec(v___y_3559_);
                                                            leanh::lean_dec_ref(v___y_3558_);
                                                            leanh::lean_dec(v___y_3557_);
                                                            leanh::lean_dec_ref(v___y_3556_);
                                                            leanh::lean_dec_ref(v_e_3555_);
                                                            leanh::lean_dec(v_mvarId_3554_);
                                                            v_a_3649_ = leanh::lean_ctor_get(
                                                                v___x_3603_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_3656_ =
                                                                (!leanh::lean_is_exclusive(
                                                                    v___x_3603_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_3656_ == 0 {
                                                                v___x_3651_ = v___x_3603_;
                                                                v_isShared_3652_ =
                                                                    v_isSharedCheck_3656_;
                                                                state = 12;
                                                                continue;
                                                            } else {
                                                                leanh::lean_inc(v_a_3649_);
                                                                leanh::lean_dec(v___x_3603_);
                                                                v___x_3651_ =
                                                                    leanh::lean_box(0);
                                                                v_isShared_3652_ =
                                                                    v_isSharedCheck_3656_;
                                                                state = 12;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        leanh::lean_dec(v_a_3579_);
                                                        leanh::lean_dec(v_a_3566_);
                                                        v___x_3657_ =
                                                            l_Lean_Expr_fvarId_x21(v_e_3555_);
                                                        leanh::lean_dec_ref(v_e_3555_);
                                                        v___x_3658_ = l_Lean_Meta_Grind_cases___lam__0___closed__0;
                                                        v___x_3659_ =
                                                            l_Lean_Meta_Grind_cases___lam__0(
                                                                v_a_3574_,
                                                                v_a_3562_,
                                                                v_mvarId_3554_,
                                                                v___x_3657_,
                                                                v___x_3658_,
                                                                v___y_3556_,
                                                                v___y_3557_,
                                                                v___y_3558_,
                                                                v___y_3559_,
                                                            );
                                                        leanh::lean_dec(v___y_3559_);
                                                        leanh::lean_dec_ref(v___y_3558_);
                                                        leanh::lean_dec(v___y_3557_);
                                                        leanh::lean_dec_ref(v___y_3556_);
                                                        return v___x_3659_;
                                                    }
                                                } else {
                                                    leanh::lean_dec(v_a_3574_);
                                                    leanh::lean_dec(v_a_3566_);
                                                    leanh::lean_dec(v_a_3562_);
                                                    leanh::lean_dec(v___y_3559_);
                                                    leanh::lean_dec_ref(v___y_3558_);
                                                    leanh::lean_dec(v___y_3557_);
                                                    leanh::lean_dec_ref(v___y_3556_);
                                                    leanh::lean_dec_ref(v_e_3555_);
                                                    leanh::lean_dec(v_mvarId_3554_);
                                                    v_a_3660_ =
                                                        leanh::lean_ctor_get(v___x_3578_, 0);
                                                    v_isSharedCheck_3667_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v___x_3578_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_3667_ == 0 {
                                                        v___x_3662_ = v___x_3578_;
                                                        v_isShared_3663_ = v_isSharedCheck_3667_;
                                                        state = 14;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_a_3660_);
                                                        leanh::lean_dec(v___x_3578_);
                                                        v___x_3662_ = leanh::lean_box(0);
                                                        v_isShared_3663_ = v_isSharedCheck_3667_;
                                                        state = 14;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                leanh::lean_dec(v_a_3566_);
                                                v___x_3668_ = l_Lean_Meta_generalizeIndices_x27(
                                                    v_mvarId_3554_,
                                                    v_e_3555_,
                                                    v___x_3572_,
                                                    v___y_3556_,
                                                    v___y_3557_,
                                                    v___y_3558_,
                                                    v___y_3559_,
                                                );
                                                if leanh::lean_obj_tag(v___x_3668_) == 0 {
                                                    v_a_3669_ =
                                                        leanh::lean_ctor_get(v___x_3668_, 0);
                                                    leanh::lean_inc(v_a_3669_);
                                                    leanh::lean_dec_ref_known(
                                                        v___x_3668_,
                                                        1,
                                                    );
                                                    v_mvarId_3670_ =
                                                        leanh::lean_ctor_get(v_a_3669_, 0);
                                                    leanh::lean_inc_n(v_mvarId_3670_, 2);
                                                    v_indicesFVarIds_3671_ =
                                                        leanh::lean_ctor_get(v_a_3669_, 1);
                                                    leanh::lean_inc_ref(
                                                        v_indicesFVarIds_3671_,
                                                    );
                                                    v_fvarId_3672_ =
                                                        leanh::lean_ctor_get(v_a_3669_, 2);
                                                    leanh::lean_inc(v_fvarId_3672_);
                                                    leanh::lean_dec(v_a_3669_);
                                                    v___x_3673_ = leanh::lean_alloc_closure(
                                                        l_Lean_Meta_Grind_cases___lam__0___boxed
                                                            as *mut core::ffi::c_void,
                                                        10,
                                                        5,
                                                    );
                                                    leanh::lean_closure_set(
                                                        v___x_3673_,
                                                        0,
                                                        v_a_3574_,
                                                    );
                                                    leanh::lean_closure_set(
                                                        v___x_3673_,
                                                        1,
                                                        v_a_3562_,
                                                    );
                                                    leanh::lean_closure_set(
                                                        v___x_3673_,
                                                        2,
                                                        v_mvarId_3670_,
                                                    );
                                                    leanh::lean_closure_set(
                                                        v___x_3673_,
                                                        3,
                                                        v_fvarId_3672_,
                                                    );
                                                    leanh::lean_closure_set(
                                                        v___x_3673_,
                                                        4,
                                                        v_indicesFVarIds_3671_,
                                                    );
                                                    v___x_3674_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(v_mvarId_3670_, v___x_3673_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_);
                                                    leanh::lean_dec(v___y_3559_);
                                                    leanh::lean_dec_ref(v___y_3558_);
                                                    leanh::lean_dec(v___y_3557_);
                                                    leanh::lean_dec_ref(v___y_3556_);
                                                    return v___x_3674_;
                                                } else {
                                                    leanh::lean_dec(v_a_3574_);
                                                    leanh::lean_dec(v_a_3562_);
                                                    leanh::lean_dec(v___y_3559_);
                                                    leanh::lean_dec_ref(v___y_3558_);
                                                    leanh::lean_dec(v___y_3557_);
                                                    leanh::lean_dec_ref(v___y_3556_);
                                                    v_a_3675_ =
                                                        leanh::lean_ctor_get(v___x_3668_, 0);
                                                    v_isSharedCheck_3682_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v___x_3668_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_3682_ == 0 {
                                                        v___x_3677_ = v___x_3668_;
                                                        v_isShared_3678_ = v_isSharedCheck_3682_;
                                                        state = 16;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_a_3675_);
                                                        leanh::lean_dec(v___x_3668_);
                                                        v___x_3677_ = leanh::lean_box(0);
                                                        v_isShared_3678_ = v_isSharedCheck_3682_;
                                                        state = 16;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            leanh::lean_dec(v_a_3566_);
                                            leanh::lean_dec(v_a_3562_);
                                            leanh::lean_dec(v___y_3559_);
                                            leanh::lean_dec_ref(v___y_3558_);
                                            leanh::lean_dec(v___y_3557_);
                                            leanh::lean_dec_ref(v___y_3556_);
                                            leanh::lean_dec_ref(v_e_3555_);
                                            leanh::lean_dec(v_mvarId_3554_);
                                            v_a_3683_ = leanh::lean_ctor_get(v___x_3573_, 0);
                                            v_isSharedCheck_3690_ =
                                                (!leanh::lean_is_exclusive(v___x_3573_))
                                                    as u8;
                                            if v_isSharedCheck_3690_ == 0 {
                                                v___x_3685_ = v___x_3573_;
                                                v_isShared_3686_ = v_isSharedCheck_3690_;
                                                state = 18;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_3683_);
                                                leanh::lean_dec(v___x_3573_);
                                                v___x_3685_ = leanh::lean_box(0);
                                                v_isShared_3686_ = v_isSharedCheck_3690_;
                                                state = 18;
                                                continue;
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec(v_a_3570_);
                                        leanh::lean_dec(v_declName_3568_);
                                        leanh::lean_dec(v_a_3562_);
                                        v___x_3691_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg(v_mvarId_3554_, v_e_3555_, v_a_3566_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_);
                                        leanh::lean_dec(v___y_3559_);
                                        leanh::lean_dec_ref(v___y_3558_);
                                        leanh::lean_dec(v___y_3557_);
                                        leanh::lean_dec_ref(v___y_3556_);
                                        return v___x_3691_;
                                    }
                                } else {
                                    leanh::lean_dec(v_declName_3568_);
                                    leanh::lean_dec(v_a_3566_);
                                    leanh::lean_dec(v_a_3562_);
                                    leanh::lean_dec(v___y_3559_);
                                    leanh::lean_dec_ref(v___y_3558_);
                                    leanh::lean_dec(v___y_3557_);
                                    leanh::lean_dec_ref(v___y_3556_);
                                    leanh::lean_dec_ref(v_e_3555_);
                                    leanh::lean_dec(v_mvarId_3554_);
                                    v_a_3692_ = leanh::lean_ctor_get(v___x_3569_, 0);
                                    v_isSharedCheck_3699_ =
                                        (!leanh::lean_is_exclusive(v___x_3569_)) as u8;
                                    if v_isSharedCheck_3699_ == 0 {
                                        v___x_3694_ = v___x_3569_;
                                        v_isShared_3695_ = v_isSharedCheck_3699_;
                                        state = 20;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3692_);
                                        leanh::lean_dec(v___x_3569_);
                                        v___x_3694_ = leanh::lean_box(0);
                                        v_isShared_3695_ = v_isSharedCheck_3699_;
                                        state = 20;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_3567_);
                                leanh::lean_dec(v_a_3562_);
                                v___x_3700_ = l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_cases_throwInductiveExpected___redArg(v_mvarId_3554_, v_e_3555_, v_a_3566_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_);
                                leanh::lean_dec(v___y_3559_);
                                leanh::lean_dec_ref(v___y_3558_);
                                leanh::lean_dec(v___y_3557_);
                                leanh::lean_dec_ref(v___y_3556_);
                                return v___x_3700_;
                            }
                        } else {
                            leanh::lean_dec(v_a_3562_);
                            leanh::lean_dec(v___y_3559_);
                            leanh::lean_dec_ref(v___y_3558_);
                            leanh::lean_dec(v___y_3557_);
                            leanh::lean_dec_ref(v___y_3556_);
                            leanh::lean_dec_ref(v_e_3555_);
                            leanh::lean_dec(v_mvarId_3554_);
                            v_a_3701_ = leanh::lean_ctor_get(v___x_3565_, 0);
                            v_isSharedCheck_3708_ =
                                (!leanh::lean_is_exclusive(v___x_3565_)) as u8;
                            if v_isSharedCheck_3708_ == 0 {
                                v___x_3703_ = v___x_3565_;
                                v_isShared_3704_ = v_isSharedCheck_3708_;
                                state = 22;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3701_);
                                leanh::lean_dec(v___x_3565_);
                                v___x_3703_ = leanh::lean_box(0);
                                v_isShared_3704_ = v_isSharedCheck_3708_;
                                state = 22;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_3562_);
                        leanh::lean_dec(v___y_3559_);
                        leanh::lean_dec_ref(v___y_3558_);
                        leanh::lean_dec(v___y_3557_);
                        leanh::lean_dec_ref(v___y_3556_);
                        leanh::lean_dec_ref(v_e_3555_);
                        leanh::lean_dec(v_mvarId_3554_);
                        v_a_3709_ = leanh::lean_ctor_get(v___x_3563_, 0);
                        v_isSharedCheck_3716_ =
                            (!leanh::lean_is_exclusive(v___x_3563_)) as u8;
                        if v_isSharedCheck_3716_ == 0 {
                            v___x_3711_ = v___x_3563_;
                            v_isShared_3712_ = v_isSharedCheck_3716_;
                            state = 24;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3709_);
                            leanh::lean_dec(v___x_3563_);
                            v___x_3711_ = leanh::lean_box(0);
                            v_isShared_3712_ = v_isSharedCheck_3716_;
                            state = 24;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_3559_);
                    leanh::lean_dec_ref(v___y_3558_);
                    leanh::lean_dec(v___y_3557_);
                    leanh::lean_dec_ref(v___y_3556_);
                    leanh::lean_dec_ref(v_e_3555_);
                    leanh::lean_dec(v_mvarId_3554_);
                    v_a_3717_ = leanh::lean_ctor_get(v___x_3561_, 0);
                    v_isSharedCheck_3724_ = (!leanh::lean_is_exclusive(v___x_3561_)) as u8;
                    if v_isSharedCheck_3724_ == 0 {
                        v___x_3719_ = v___x_3561_;
                        v_isShared_3720_ = v_isSharedCheck_3724_;
                        state = 26;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3717_);
                        leanh::lean_dec(v___x_3561_);
                        v___x_3719_ = leanh::lean_box(0);
                        v_isShared_3720_ = v_isSharedCheck_3724_;
                        state = 26;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3586_ = (leanh::lean_unbox(v_a_3579_) as u8);
                leanh::lean_dec(v_a_3579_);
                v___x_3587_ = l_Lean_Meta_intro1Core(
                    v_mvarId_3581_,
                    v___x_3586_,
                    v___y_3582_,
                    v___y_3583_,
                    v___y_3584_,
                    v___y_3585_,
                );
                if leanh::lean_obj_tag(v___x_3587_) == 0 {
                    v_a_3588_ = leanh::lean_ctor_get(v___x_3587_, 0);
                    leanh::lean_inc(v_a_3588_);
                    leanh::lean_dec_ref_known(v___x_3587_, 1);
                    v_fst_3589_ = leanh::lean_ctor_get(v_a_3588_, 0);
                    leanh::lean_inc(v_fst_3589_);
                    v_snd_3590_ = leanh::lean_ctor_get(v_a_3588_, 1);
                    leanh::lean_inc_n(v_snd_3590_, 2);
                    leanh::lean_dec(v_a_3588_);
                    v___x_3591_ = l_Lean_Meta_Grind_cases___lam__0___closed__0;
                    v___x_3592_ = leanh::lean_alloc_closure(
                        l_Lean_Meta_Grind_cases___lam__0___boxed as *mut core::ffi::c_void,
                        10,
                        5,
                    );
                    leanh::lean_closure_set(v___x_3592_, 0, v_a_3574_);
                    leanh::lean_closure_set(v___x_3592_, 1, v_a_3562_);
                    leanh::lean_closure_set(v___x_3592_, 2, v_snd_3590_);
                    leanh::lean_closure_set(v___x_3592_, 3, v_fst_3589_);
                    leanh::lean_closure_set(v___x_3592_, 4, v___x_3591_);
                    v___x_3593_ =
                        l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(
                            v_snd_3590_,
                            v___x_3592_,
                            v___y_3582_,
                            v___y_3583_,
                            v___y_3584_,
                            v___y_3585_,
                        );
                    leanh::lean_dec(v___y_3585_);
                    leanh::lean_dec_ref(v___y_3584_);
                    leanh::lean_dec(v___y_3583_);
                    leanh::lean_dec_ref(v___y_3582_);
                    return v___x_3593_;
                } else {
                    leanh::lean_dec(v___y_3585_);
                    leanh::lean_dec_ref(v___y_3584_);
                    leanh::lean_dec(v___y_3583_);
                    leanh::lean_dec_ref(v___y_3582_);
                    leanh::lean_dec(v_a_3574_);
                    leanh::lean_dec(v_a_3562_);
                    v_a_3594_ = leanh::lean_ctor_get(v___x_3587_, 0);
                    v_isSharedCheck_3601_ = (!leanh::lean_is_exclusive(v___x_3587_)) as u8;
                    if v_isSharedCheck_3601_ == 0 {
                        v___x_3596_ = v___x_3587_;
                        v_isShared_3597_ = v_isSharedCheck_3601_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3594_);
                        leanh::lean_dec(v___x_3587_);
                        v___x_3596_ = leanh::lean_box(0);
                        v_isShared_3597_ = v_isSharedCheck_3601_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3597_ == 0 {
                    v___x_3599_ = v___x_3596_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3600_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_a_3594_);
                    v___x_3599_ = v_reuseFailAlloc_3600_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3599_;
            }
            4 => {
                if v_isShared_3615_ == 0 {
                    v___x_3617_ = v___x_3614_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3618_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3612_);
                    v___x_3617_ = v_reuseFailAlloc_3618_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3617_;
            }
            6 => {
                if v_isShared_3623_ == 0 {
                    v___x_3625_ = v___x_3622_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3626_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_a_3620_);
                    v___x_3625_ = v_reuseFailAlloc_3626_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3625_;
            }
            8 => {
                if v_isShared_3636_ == 0 {
                    v___x_3638_ = v___x_3635_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3639_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_a_3633_);
                    v___x_3638_ = v_reuseFailAlloc_3639_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3638_;
            }
            10 => {
                if v_isShared_3644_ == 0 {
                    v___x_3646_ = v___x_3643_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3647_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_a_3641_);
                    v___x_3646_ = v_reuseFailAlloc_3647_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3646_;
            }
            12 => {
                if v_isShared_3652_ == 0 {
                    v___x_3654_ = v___x_3651_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3655_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3655_, 0, v_a_3649_);
                    v___x_3654_ = v_reuseFailAlloc_3655_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3654_;
            }
            14 => {
                if v_isShared_3663_ == 0 {
                    v___x_3665_ = v___x_3662_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3666_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_a_3660_);
                    v___x_3665_ = v_reuseFailAlloc_3666_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3665_;
            }
            16 => {
                if v_isShared_3678_ == 0 {
                    v___x_3680_ = v___x_3677_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3681_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_a_3675_);
                    v___x_3680_ = v_reuseFailAlloc_3681_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3680_;
            }
            18 => {
                if v_isShared_3686_ == 0 {
                    v___x_3688_ = v___x_3685_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3689_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_a_3683_);
                    v___x_3688_ = v_reuseFailAlloc_3689_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3688_;
            }
            20 => {
                if v_isShared_3695_ == 0 {
                    v___x_3697_ = v___x_3694_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3698_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_a_3692_);
                    v___x_3697_ = v_reuseFailAlloc_3698_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_3697_;
            }
            22 => {
                if v_isShared_3704_ == 0 {
                    v___x_3706_ = v___x_3703_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3707_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_a_3701_);
                    v___x_3706_ = v_reuseFailAlloc_3707_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_3706_;
            }
            24 => {
                if v_isShared_3712_ == 0 {
                    v___x_3714_ = v___x_3711_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3715_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_a_3709_);
                    v___x_3714_ = v_reuseFailAlloc_3715_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_3714_;
            }
            26 => {
                if v_isShared_3720_ == 0 {
                    v___x_3722_ = v___x_3719_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3723_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_a_3717_);
                    v___x_3722_ = v_reuseFailAlloc_3723_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_3722_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_cases___lam__1___boxed(
    mut v_mvarId_3725_: *mut leanh::LeanObject,
    mut v_e_3726_: *mut leanh::LeanObject,
    mut v___y_3727_: *mut leanh::LeanObject,
    mut v___y_3728_: *mut leanh::LeanObject,
    mut v___y_3729_: *mut leanh::LeanObject,
    mut v___y_3730_: *mut leanh::LeanObject,
    mut v___y_3731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3732_ = l_Lean_Meta_Grind_cases___lam__1(
        v_mvarId_3725_,
        v_e_3726_,
        v___y_3727_,
        v___y_3728_,
        v___y_3729_,
        v___y_3730_,
    );
    return v_res_3732_;
}
pub unsafe fn l_Lean_Meta_Grind_cases(
    mut v_mvarId_3733_: *mut leanh::LeanObject,
    mut v_e_3734_: *mut leanh::LeanObject,
    mut v_a_3735_: *mut leanh::LeanObject,
    mut v_a_3736_: *mut leanh::LeanObject,
    mut v_a_3737_: *mut leanh::LeanObject,
    mut v_a_3738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_mvarId_3733_);
    v___f_3740_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_cases___lam__1___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___f_3740_, 0, v_mvarId_3733_);
    leanh::lean_closure_set(v___f_3740_, 1, v_e_3734_);
    v___x_3741_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_cases_spec__5___redArg(
        v_mvarId_3733_,
        v___f_3740_,
        v_a_3735_,
        v_a_3736_,
        v_a_3737_,
        v_a_3738_,
    );
    return v___x_3741_;
}
pub unsafe fn l_Lean_Meta_Grind_cases___boxed(
    mut v_mvarId_3742_: *mut leanh::LeanObject,
    mut v_e_3743_: *mut leanh::LeanObject,
    mut v_a_3744_: *mut leanh::LeanObject,
    mut v_a_3745_: *mut leanh::LeanObject,
    mut v_a_3746_: *mut leanh::LeanObject,
    mut v_a_3747_: *mut leanh::LeanObject,
    mut v_a_3748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3749_ = l_Lean_Meta_Grind_cases(
        v_mvarId_3742_,
        v_e_3743_,
        v_a_3744_,
        v_a_3745_,
        v_a_3746_,
        v_a_3747_,
    );
    leanh::lean_dec(v_a_3747_);
    leanh::lean_dec_ref(v_a_3746_);
    leanh::lean_dec(v_a_3745_);
    leanh::lean_dec_ref(v_a_3744_);
    return v_res_3749_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1(
    mut v_mvarId_3750_: *mut leanh::LeanObject,
    mut v_val_3751_: *mut leanh::LeanObject,
    mut v___y_3752_: *mut leanh::LeanObject,
    mut v___y_3753_: *mut leanh::LeanObject,
    mut v___y_3754_: *mut leanh::LeanObject,
    mut v___y_3755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3757_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___redArg(
        v_mvarId_3750_,
        v_val_3751_,
        v___y_3753_,
    );
    return v___x_3757_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1___boxed(
    mut v_mvarId_3758_: *mut leanh::LeanObject,
    mut v_val_3759_: *mut leanh::LeanObject,
    mut v___y_3760_: *mut leanh::LeanObject,
    mut v___y_3761_: *mut leanh::LeanObject,
    mut v___y_3762_: *mut leanh::LeanObject,
    mut v___y_3763_: *mut leanh::LeanObject,
    mut v___y_3764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3765_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1(
        v_mvarId_3758_,
        v_val_3759_,
        v___y_3760_,
        v___y_3761_,
        v___y_3762_,
        v___y_3763_,
    );
    leanh::lean_dec(v___y_3763_);
    leanh::lean_dec_ref(v___y_3762_);
    leanh::lean_dec(v___y_3761_);
    leanh::lean_dec_ref(v___y_3760_);
    return v_res_3765_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3(
    mut v_upperBound_3766_: *mut leanh::LeanObject,
    mut v___y_3767_: *mut leanh::LeanObject,
    mut v___x_3768_: *mut leanh::LeanObject,
    mut v___x_3769_: *mut leanh::LeanObject,
    mut v_a_3770_: *mut leanh::LeanObject,
    mut v_mvarId_3771_: *mut leanh::LeanObject,
    mut v_inst_3772_: *mut leanh::LeanObject,
    mut v_R_3773_: *mut leanh::LeanObject,
    mut v_a_3774_: *mut leanh::LeanObject,
    mut v_b_3775_: *mut leanh::LeanObject,
    mut v_c_3776_: *mut leanh::LeanObject,
    mut v___y_3777_: *mut leanh::LeanObject,
    mut v___y_3778_: *mut leanh::LeanObject,
    mut v___y_3779_: *mut leanh::LeanObject,
    mut v___y_3780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3782_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___redArg(
        v_upperBound_3766_,
        v___y_3767_,
        v___x_3768_,
        v___x_3769_,
        v_a_3770_,
        v_mvarId_3771_,
        v_a_3774_,
        v_b_3775_,
        v___y_3777_,
        v___y_3778_,
        v___y_3779_,
        v___y_3780_,
    );
    return v___x_3782_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3___boxed(
    mut v_upperBound_3783_: *mut leanh::LeanObject,
    mut v___y_3784_: *mut leanh::LeanObject,
    mut v___x_3785_: *mut leanh::LeanObject,
    mut v___x_3786_: *mut leanh::LeanObject,
    mut v_a_3787_: *mut leanh::LeanObject,
    mut v_mvarId_3788_: *mut leanh::LeanObject,
    mut v_inst_3789_: *mut leanh::LeanObject,
    mut v_R_3790_: *mut leanh::LeanObject,
    mut v_a_3791_: *mut leanh::LeanObject,
    mut v_b_3792_: *mut leanh::LeanObject,
    mut v_c_3793_: *mut leanh::LeanObject,
    mut v___y_3794_: *mut leanh::LeanObject,
    mut v___y_3795_: *mut leanh::LeanObject,
    mut v___y_3796_: *mut leanh::LeanObject,
    mut v___y_3797_: *mut leanh::LeanObject,
    mut v___y_3798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3799_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_cases_spec__3(
        v_upperBound_3783_,
        v___y_3784_,
        v___x_3785_,
        v___x_3786_,
        v_a_3787_,
        v_mvarId_3788_,
        v_inst_3789_,
        v_R_3790_,
        v_a_3791_,
        v_b_3792_,
        v_c_3793_,
        v___y_3794_,
        v___y_3795_,
        v___y_3796_,
        v___y_3797_,
    );
    leanh::lean_dec(v___y_3797_);
    leanh::lean_dec_ref(v___y_3796_);
    leanh::lean_dec(v___y_3795_);
    leanh::lean_dec_ref(v___y_3794_);
    leanh::lean_dec(v___x_3786_);
    leanh::lean_dec(v_upperBound_3783_);
    return v_res_3799_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0(
    mut v_00_u03b1_3800_: *mut leanh::LeanObject,
    mut v_constName_3801_: *mut leanh::LeanObject,
    mut v___y_3802_: *mut leanh::LeanObject,
    mut v___y_3803_: *mut leanh::LeanObject,
    mut v___y_3804_: *mut leanh::LeanObject,
    mut v___y_3805_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3807_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___redArg(v_constName_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_);
    return v___x_3807_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0___boxed(
    mut v_00_u03b1_3808_: *mut leanh::LeanObject,
    mut v_constName_3809_: *mut leanh::LeanObject,
    mut v___y_3810_: *mut leanh::LeanObject,
    mut v___y_3811_: *mut leanh::LeanObject,
    mut v___y_3812_: *mut leanh::LeanObject,
    mut v___y_3813_: *mut leanh::LeanObject,
    mut v___y_3814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3815_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0(v_00_u03b1_3808_, v_constName_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_);
    leanh::lean_dec(v___y_3813_);
    leanh::lean_dec_ref(v___y_3812_);
    leanh::lean_dec(v___y_3811_);
    leanh::lean_dec_ref(v___y_3810_);
    return v_res_3815_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2(
    mut v_00_u03b2_3816_: *mut leanh::LeanObject,
    mut v_x_3817_: *mut leanh::LeanObject,
    mut v_x_3818_: *mut leanh::LeanObject,
    mut v_x_3819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3820_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2___redArg(v_x_3817_, v_x_3818_, v_x_3819_);
    return v___x_3820_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2(
    mut v_00_u03b1_3821_: *mut leanh::LeanObject,
    mut v_ref_3822_: *mut leanh::LeanObject,
    mut v_constName_3823_: *mut leanh::LeanObject,
    mut v___y_3824_: *mut leanh::LeanObject,
    mut v___y_3825_: *mut leanh::LeanObject,
    mut v___y_3826_: *mut leanh::LeanObject,
    mut v___y_3827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3829_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___redArg(v_ref_3822_, v_constName_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
    return v___x_3829_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b1_3830_: *mut leanh::LeanObject,
    mut v_ref_3831_: *mut leanh::LeanObject,
    mut v_constName_3832_: *mut leanh::LeanObject,
    mut v___y_3833_: *mut leanh::LeanObject,
    mut v___y_3834_: *mut leanh::LeanObject,
    mut v___y_3835_: *mut leanh::LeanObject,
    mut v___y_3836_: *mut leanh::LeanObject,
    mut v___y_3837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3838_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2(v_00_u03b1_3830_, v_ref_3831_, v_constName_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
    leanh::lean_dec(v___y_3836_);
    leanh::lean_dec_ref(v___y_3835_);
    leanh::lean_dec(v___y_3834_);
    leanh::lean_dec_ref(v___y_3833_);
    leanh::lean_dec(v_ref_3831_);
    return v_res_3838_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5(
    mut v_00_u03b2_3839_: *mut leanh::LeanObject,
    mut v_x_3840_: *mut leanh::LeanObject,
    mut v_x_3841_: usize,
    mut v_x_3842_: usize,
    mut v_x_3843_: *mut leanh::LeanObject,
    mut v_x_3844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3845_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___redArg(v_x_3840_, v_x_3841_, v_x_3842_, v_x_3843_, v_x_3844_);
    return v___x_3845_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b2_3846_: *mut leanh::LeanObject,
    mut v_x_3847_: *mut leanh::LeanObject,
    mut v_x_3848_: *mut leanh::LeanObject,
    mut v_x_3849_: *mut leanh::LeanObject,
    mut v_x_3850_: *mut leanh::LeanObject,
    mut v_x_3851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_13910__boxed_3852_: usize = 0;
    let mut v_x_13911__boxed_3853_: usize = 0;
    let mut v_res_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_13910__boxed_3852_ = leanh::lean_unbox_usize(v_x_3848_);
    leanh::lean_dec(v_x_3848_);
    v_x_13911__boxed_3853_ = leanh::lean_unbox_usize(v_x_3849_);
    leanh::lean_dec(v_x_3849_);
    v_res_3854_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5(v_00_u03b2_3846_, v_x_3847_, v_x_13910__boxed_3852_, v_x_13911__boxed_3853_, v_x_3850_, v_x_3851_);
    return v_res_3854_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7(
    mut v_00_u03b1_3855_: *mut leanh::LeanObject,
    mut v_ref_3856_: *mut leanh::LeanObject,
    mut v_msg_3857_: *mut leanh::LeanObject,
    mut v_declHint_3858_: *mut leanh::LeanObject,
    mut v___y_3859_: *mut leanh::LeanObject,
    mut v___y_3860_: *mut leanh::LeanObject,
    mut v___y_3861_: *mut leanh::LeanObject,
    mut v___y_3862_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3864_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___redArg(v_ref_3856_, v_msg_3857_, v_declHint_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_);
    return v___x_3864_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7___boxed(
    mut v_00_u03b1_3865_: *mut leanh::LeanObject,
    mut v_ref_3866_: *mut leanh::LeanObject,
    mut v_msg_3867_: *mut leanh::LeanObject,
    mut v_declHint_3868_: *mut leanh::LeanObject,
    mut v___y_3869_: *mut leanh::LeanObject,
    mut v___y_3870_: *mut leanh::LeanObject,
    mut v___y_3871_: *mut leanh::LeanObject,
    mut v___y_3872_: *mut leanh::LeanObject,
    mut v___y_3873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3874_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7(v_00_u03b1_3865_, v_ref_3866_, v_msg_3867_, v_declHint_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
    leanh::lean_dec(v___y_3872_);
    leanh::lean_dec_ref(v___y_3871_);
    leanh::lean_dec(v___y_3870_);
    leanh::lean_dec_ref(v___y_3869_);
    leanh::lean_dec(v_ref_3866_);
    return v_res_3874_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10(
    mut v_00_u03b2_3875_: *mut leanh::LeanObject,
    mut v_n_3876_: *mut leanh::LeanObject,
    mut v_k_3877_: *mut leanh::LeanObject,
    mut v_v_3878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3879_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10___redArg(v_n_3876_, v_k_3877_, v_v_3878_);
    return v___x_3879_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11(
    mut v_00_u03b2_3880_: *mut leanh::LeanObject,
    mut v_depth_3881_: usize,
    mut v_keys_3882_: *mut leanh::LeanObject,
    mut v_vals_3883_: *mut leanh::LeanObject,
    mut v_heq_3884_: *mut leanh::LeanObject,
    mut v_i_3885_: *mut leanh::LeanObject,
    mut v_entries_3886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3887_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___redArg(v_depth_3881_, v_keys_3882_, v_vals_3883_, v_i_3885_, v_entries_3886_);
    return v___x_3887_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11___boxed(
    mut v_00_u03b2_3888_: *mut leanh::LeanObject,
    mut v_depth_3889_: *mut leanh::LeanObject,
    mut v_keys_3890_: *mut leanh::LeanObject,
    mut v_vals_3891_: *mut leanh::LeanObject,
    mut v_heq_3892_: *mut leanh::LeanObject,
    mut v_i_3893_: *mut leanh::LeanObject,
    mut v_entries_3894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_3895_: usize = 0;
    let mut v_res_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3895_ = leanh::lean_unbox_usize(v_depth_3889_);
    leanh::lean_dec(v_depth_3889_);
    v_res_3896_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__11(v_00_u03b2_3888_, v_depth_boxed_3895_, v_keys_3890_, v_vals_3891_, v_heq_3892_, v_i_3893_, v_entries_3894_);
    leanh::lean_dec_ref(v_vals_3891_);
    leanh::lean_dec_ref(v_keys_3890_);
    return v_res_3896_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11(
    mut v_msg_3897_: *mut leanh::LeanObject,
    mut v_declHint_3898_: *mut leanh::LeanObject,
    mut v___y_3899_: *mut leanh::LeanObject,
    mut v___y_3900_: *mut leanh::LeanObject,
    mut v___y_3901_: *mut leanh::LeanObject,
    mut v___y_3902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3904_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___redArg(v_msg_3897_, v_declHint_3898_, v___y_3902_);
    return v___x_3904_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11___boxed(
    mut v_msg_3905_: *mut leanh::LeanObject,
    mut v_declHint_3906_: *mut leanh::LeanObject,
    mut v___y_3907_: *mut leanh::LeanObject,
    mut v___y_3908_: *mut leanh::LeanObject,
    mut v___y_3909_: *mut leanh::LeanObject,
    mut v___y_3910_: *mut leanh::LeanObject,
    mut v___y_3911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3912_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__9_spec__11(v_msg_3905_, v_declHint_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_);
    leanh::lean_dec(v___y_3910_);
    leanh::lean_dec_ref(v___y_3909_);
    leanh::lean_dec(v___y_3908_);
    leanh::lean_dec_ref(v___y_3907_);
    return v_res_3912_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10(
    mut v_00_u03b1_3913_: *mut leanh::LeanObject,
    mut v_ref_3914_: *mut leanh::LeanObject,
    mut v_msg_3915_: *mut leanh::LeanObject,
    mut v___y_3916_: *mut leanh::LeanObject,
    mut v___y_3917_: *mut leanh::LeanObject,
    mut v___y_3918_: *mut leanh::LeanObject,
    mut v___y_3919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3921_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(v_ref_3914_, v_msg_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_);
    return v___x_3921_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10___boxed(
    mut v_00_u03b1_3922_: *mut leanh::LeanObject,
    mut v_ref_3923_: *mut leanh::LeanObject,
    mut v_msg_3924_: *mut leanh::LeanObject,
    mut v___y_3925_: *mut leanh::LeanObject,
    mut v___y_3926_: *mut leanh::LeanObject,
    mut v___y_3927_: *mut leanh::LeanObject,
    mut v___y_3928_: *mut leanh::LeanObject,
    mut v___y_3929_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3930_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10(v_00_u03b1_3922_, v_ref_3923_, v_msg_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_);
    leanh::lean_dec(v___y_3928_);
    leanh::lean_dec_ref(v___y_3927_);
    leanh::lean_dec(v___y_3926_);
    leanh::lean_dec_ref(v___y_3925_);
    leanh::lean_dec(v_ref_3923_);
    return v_res_3930_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10_spec__13(
    mut v_00_u03b2_3931_: *mut leanh::LeanObject,
    mut v_x_3932_: *mut leanh::LeanObject,
    mut v_x_3933_: *mut leanh::LeanObject,
    mut v_x_3934_: *mut leanh::LeanObject,
    mut v_x_3935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3936_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_cases_spec__1_spec__2_spec__5_spec__10_spec__13___redArg(v_x_3932_, v_x_3933_, v_x_3934_, v_x_3935_);
    return v___x_3936_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13(
    mut v_00_u03b1_3937_: *mut leanh::LeanObject,
    mut v_msg_3938_: *mut leanh::LeanObject,
    mut v___y_3939_: *mut leanh::LeanObject,
    mut v___y_3940_: *mut leanh::LeanObject,
    mut v___y_3941_: *mut leanh::LeanObject,
    mut v___y_3942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3944_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(v_msg_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_);
    return v___x_3944_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___boxed(
    mut v_00_u03b1_3945_: *mut leanh::LeanObject,
    mut v_msg_3946_: *mut leanh::LeanObject,
    mut v___y_3947_: *mut leanh::LeanObject,
    mut v___y_3948_: *mut leanh::LeanObject,
    mut v___y_3949_: *mut leanh::LeanObject,
    mut v___y_3950_: *mut leanh::LeanObject,
    mut v___y_3951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3952_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Grind_cases_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13(v_00_u03b1_3945_, v_msg_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_);
    leanh::lean_dec(v___y_3950_);
    leanh::lean_dec_ref(v___y_3949_);
    leanh::lean_dec(v___y_3948_);
    leanh::lean_dec_ref(v___y_3947_);
    return v_res_3952_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Cases(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Cases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Extension(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases =
        _init_l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases();
    leanh::lean_mark_persistent(
        l___private_Lean_Meta_Tactic_Grind_Cases_0__Lean_Meta_Grind_builtinEagerCases,
    );
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Cases(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Cases(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Cases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Extension(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Cases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Cases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Cases(builtin);
}