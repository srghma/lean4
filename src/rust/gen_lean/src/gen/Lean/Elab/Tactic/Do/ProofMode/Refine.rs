// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Refine
// Imports: Lean.Elab.Tactic.Do.ProofMode.Assumption
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_size,
    lean_array_to_list, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_string_dec_eq, lean_uint64_of_nat, lean_uint64_shift_right,
    lean_uint64_to_usize, lean_uint64_xor, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_le,
    lean_usize_dec_lt, lean_usize_land, lean_usize_mul, lean_usize_of_nat, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_TSepArray_getElems___redArg, l_Lean_Syntax_instReprTSyntax_repr___redArg,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed,
    l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs,
    l_Lean_Syntax_getId, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_Lean_maxRecDepthErrorMessage, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_isMarkedMeta;
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_empty, l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_SavedState_restore___redArg, l_Lean_Elab_Tactic_evalTactic,
    l_Lean_Elab_Tactic_replaceMainGoal___redArg, l_Lean_Elab_Tactic_saveState___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute, l_Lean_Elab_Tactic_withoutRecover___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Assumption::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption,
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Basic::l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg;
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Exact::{
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact, l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::MGoal::l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr;
use crate::r#gen::Lean::Elab::Tactic::ElabTerm::l_Lean_Elab_Tactic_elabTerm;
use crate::r#gen::Lean::Elab::Util::l_Lean_Elab_expandMacroImpl_x3f;
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_instInhabitedEffectiveImport_default,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_beta, l_Lean_Expr_getAppFn_x27,
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_isConstOf, l_Lean_Expr_mvarId_x21,
    l_Lean_Expr_sort___override, l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash,
    l_Lean_instInhabitedExpr, l_Lean_mkApp6, l_Lean_mkConst,
};
use crate::r#gen::Lean::ExtraModUses::{
    l___private_Lean_ExtraModUses_0__Lean_extraModUses, l_Lean_indirectModUseExt,
    l_Lean_instBEqExtraModUse_beq, l_Lean_instBEqExtraModUse_beq___boxed,
    l_Lean_instHashableExtraModUse_hash, l_Lean_instHashableExtraModUse_hash___boxed,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofList,
    l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_Meta_whnfR,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_getLevel;
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar;
use crate::r#gen::Lean::Modifiers::l_Lean_mkPrivateName;
use crate::r#gen::Lean::PrivateName::l_Lean_privateToUserName;
use crate::r#gen::Lean::ResolveName::{
    l_Lean_ResolveName_resolveGlobalName, l_Lean_ResolveName_resolveNamespace,
};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::r#gen::Std::Data::HashMap::Basic::l_Std_HashMap_instInhabited;
use crate::r#gen::Std::Tactic::Do::Syntax::l_Lean_Parser_Tactic_MRefinePat_parse___boxed;
pub static l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__1_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [98, 105, 110, 100, 101, 114, 73, 100, 101, 110, 116, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__1_value)
            as *mut leanh::LeanObject,
        13771926289831477797 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__3_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [105, 100, 101, 110, 116, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__3_value)
            as *mut leanh::LeanObject,
        5117844058249666356 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__1_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__1_value:
    leanh::LeanStringObject<53> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 53,
    m_capacity: 53,
    m_length: 52,
    m_data: [
        78, 101, 105, 116, 104, 101, 114, 32, 97, 32, 99, 111, 110, 106, 117, 110, 99, 116, 105,
        111, 110, 32, 110, 111, 114, 32, 97, 110, 32, 101, 120, 105, 115, 116, 101, 110, 116, 105,
        97, 108, 32, 113, 117, 97, 110, 116, 105, 102, 105, 101, 114, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__3_value:
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
    m_data: [
        101, 120, 105, 115, 116, 115, 95, 105, 110, 116, 114, 111, 39, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__4_value:
    leanh::LeanStringObject<55> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 55,
    m_capacity: 55,
    m_length: 53,
    m_data: [
        112, 97, 116, 116, 101, 114, 110, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 101, 108,
        97, 98, 111, 114, 97, 116, 101, 32, 116, 111, 32, 97, 32, 116, 101, 114, 109, 32, 116, 111,
        32, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 101, 32, 207, 136, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__6_value:
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
    m_data: [101, 120, 105, 115, 116, 115, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__7_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [97, 110, 100, 95, 105, 110, 116, 114, 111, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__8_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [83, 116, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9_value:
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
    m_data: [68, 111, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__10_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [83, 80, 114, 101, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__11_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [97, 110, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__11_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__8_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9_value)
            as *mut leanh::LeanObject,
        7300584325018775040 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__10_value)
            as *mut leanh::LeanObject,
        13332341187416043682 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__11_value)
            as *mut leanh::LeanObject,
        14620467112940626392 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__13_value:
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
    m_data: [77, 101, 116, 97, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__14_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [100, 101, 98, 117, 103, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__14_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__13_value)
            as *mut leanh::LeanObject,
        142734480563613395 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__14_value)
            as *mut leanh::LeanObject,
        6030293614678436448 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__16_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [116, 114, 97, 99, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__16_value)
            as *mut leanh::LeanObject,
        14231257465488249300 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__19_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [102, 58, 32, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__19_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__21_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [44, 32, 97, 114, 103, 115, 58, 32, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__21_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__23_value:
    leanh::LeanStringObject<17> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        99, 111, 117, 108, 100, 32, 110, 111, 116, 32, 115, 111, 108, 118, 101, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__23_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__25_value:
    leanh::LeanStringObject<15> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        32, 98, 121, 32, 97, 115, 115, 117, 109, 112, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__25: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__25_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__27_value:
    leanh::LeanStringObject<21> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        117, 110, 107, 110, 111, 119, 110, 32, 104, 121, 112, 111, 116, 104, 101, 115, 105, 115,
        32, 96, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__27: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__27_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__28_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__28: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__29_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__29: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__29_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__30_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__30: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__1_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__1_value) as *mut leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__0_value) as *mut leanh::LeanObject,7310567555909517314 as *mut leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__1_value) as *mut leanh::LeanObject,273128857561458264 as *mut leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg___closed__0: u64 = 0;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__7_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__7_value) as *mut leanh::LeanObject,7870113334857981723 as *mut leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__9_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__9_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__10: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__11_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__11_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__14_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__14: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__15_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__15_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__16_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__16: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__17_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__17_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__18_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__18: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__19_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__19_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__20_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__20_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__21_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__21_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__22_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__22_value) as *mut leanh::LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__3_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___closed__0_value: leanh::LeanStringObject<158> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 158, m_capacity: 158, m_length: 157, m_data: [109, 97, 120, 105, 109, 117, 109, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 32, 100, 101, 112, 116, 104, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 32, 60, 110, 117, 109, 62, 96, 32, 116, 111, 32, 105, 110, 99, 114, 101, 97, 115, 101, 32, 108, 105, 109, 105, 116, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115, 32, 116, 114, 117, 101, 96, 32, 116, 111, 32, 103, 101, 116, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 32, 105, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value:
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
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value:
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
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__2_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [109, 114, 101, 102, 105, 110, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__2_value)
            as *mut leanh::LeanObject,
        6333567104024089553 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__4_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__4_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__1_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [80, 114, 111, 111, 102, 77, 111, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__2_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 108, 97, 98, 77, 82, 101, 102, 105, 110, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__0_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9_value) as *mut leanh::LeanObject,11384710337598098789 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__1_value) as *mut leanh::LeanObject,5427134421608450815 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__2_value) as *mut leanh::LeanObject,5372934286266800045 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__1_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 13, m_data: [109, 114, 101, 102, 105, 110, 101, 80, 97, 116, 226, 159, 168, 95, 226, 159, 169, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject,14125490278268599519 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__3_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 159, 168, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__4_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 114, 101, 102, 105, 110, 101, 80, 97, 116, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__4_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__4_value) as *mut leanh::LeanObject,8766709874229489008 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__6_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__6_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__8_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 159, 169, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__0_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 13, m_data: [109, 114, 101, 102, 105, 110, 101, 80, 97, 116, 226, 140, 156, 95, 226, 140, 157, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value) as *mut leanh::LeanObject,18344149449936419494 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject,10488206668377814853 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 140, 156, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__3_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 1, m_data: [226, 140, 157, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__0_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [109, 101, 120, 105, 115, 116, 115, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__0_value)
            as *mut leanh::LeanObject,
        1667259957697292907 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__2_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [112, 97, 114, 101, 110, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__2_value)
            as *mut leanh::LeanObject,
        8689124066155232629 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__4_value:
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
    m_data: [40, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__5_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__5_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__5_value)
            as *mut leanh::LeanObject,
        8504843326314613972 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__7_value:
    leanh::LeanStringObject<19> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__7_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__7_value)
            as *mut leanh::LeanObject,
        17228437386856258271 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__9_value:
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
    m_data: [59, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__10_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [116, 97, 99, 116, 105, 99, 84, 114, 121, 95, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__10_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__10_value)
            as *mut leanh::LeanObject,
        10962186005905108258 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__12_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [116, 114, 121, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__13_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [109, 97, 115, 115, 117, 109, 112, 116, 105, 111, 110, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__13_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__13_value)
            as *mut leanh::LeanObject,
        1814919757381564531 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__15_value:
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
    m_data: [41, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__16_value:
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
    m_data: [109, 114, 101, 102, 105, 110, 101, 80, 97, 116, 63, 95, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__16_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__16_value)
            as *mut leanh::LeanObject,
        12626967213392556061 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__18_value:
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
    m_data: [63, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__19_value:
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
    m_data: [84, 101, 114, 109, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__20_value:
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
    m_data: [104, 111, 108, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__20_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__0_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__19_value)
            as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__20_value)
            as *mut leanh::LeanObject,
        3984140175429830279 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__22_value:
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
    m_data: [95, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__22_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__0_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 108, 97, 98, 77, 69, 120, 105, 115, 116, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__0_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__1_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9_value) as *mut leanh::LeanObject,11384710337598098789 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_4: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__1_value) as *mut leanh::LeanObject,5427134421608450815 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value_aux_4) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__0_value) as *mut leanh::LeanObject,8076920694872788882 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm(
    mut v_pat_2576_: *mut leanh::LeanObject,
    mut v_expected_2577_: *mut leanh::LeanObject,
    mut v_a_2578_: *mut leanh::LeanObject,
    mut v_a_2579_: *mut leanh::LeanObject,
    mut v_a_2580_: *mut leanh::LeanObject,
    mut v_a_2581_: *mut leanh::LeanObject,
    mut v_a_2582_: *mut leanh::LeanObject,
    mut v_a_2583_: *mut leanh::LeanObject,
    mut v_a_2584_: *mut leanh::LeanObject,
    mut v_a_2585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: u8 = 0;
    let mut v___x_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2602_: u8 = 0;
    let mut v___x_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2607_: u8 = 0;
    let mut v_a_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2611_: u8 = 0;
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2615_: u8 = 0;
    let mut v_h_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2620_: u8 = 0;
    let mut v___x_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: u8 = 0;
    let mut v___x_2623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: u8 = 0;
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2635_: u8 = 0;
    let mut v___x_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_pat_2576_) {
                2 => {
                    v_h_2616_ = leanh::lean_ctor_get(v_pat_2576_, 0);
                    leanh::lean_inc(v_h_2616_);
                    leanh::lean_dec_ref_known(v_pat_2576_, 1);
                    v_t_2588_ = v_h_2616_;
                    v___y_2589_ = v_a_2578_;
                    v___y_2590_ = v_a_2579_;
                    v___y_2591_ = v_a_2580_;
                    v___y_2592_ = v_a_2581_;
                    v___y_2593_ = v_a_2582_;
                    v___y_2594_ = v_a_2583_;
                    v___y_2595_ = v_a_2584_;
                    v___y_2596_ = v_a_2585_;
                    state = 1;
                    continue;
                }
                0 => {
                    v_name_2617_ = leanh::lean_ctor_get(v_pat_2576_, 0);
                    v_isSharedCheck_2635_ = (!leanh::lean_is_exclusive(v_pat_2576_)) as u8;
                    if v_isSharedCheck_2635_ == 0 {
                        v___x_2619_ = v_pat_2576_;
                        v_isShared_2620_ = v_isSharedCheck_2635_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_name_2617_);
                        leanh::lean_dec(v_pat_2576_);
                        v___x_2619_ = leanh::lean_box(0);
                        v_isShared_2620_ = v_isSharedCheck_2635_;
                        state = 6;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_dec(v_expected_2577_);
                    leanh::lean_dec_ref(v_pat_2576_);
                    v___x_2636_ = leanh::lean_box(0);
                    v___x_2637_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2637_, 0, v___x_2636_);
                    return v___x_2637_;
                }
            },
            1 => {
                v___x_2597_ = 0;
                v___x_2598_ = l_Lean_Elab_Tactic_elabTerm(
                    v_t_2588_,
                    v_expected_2577_,
                    v___x_2597_,
                    v___y_2589_,
                    v___y_2590_,
                    v___y_2591_,
                    v___y_2592_,
                    v___y_2593_,
                    v___y_2594_,
                    v___y_2595_,
                    v___y_2596_,
                );
                if leanh::lean_obj_tag(v___x_2598_) == 0 {
                    v_a_2599_ = leanh::lean_ctor_get(v___x_2598_, 0);
                    v_isSharedCheck_2607_ = (!leanh::lean_is_exclusive(v___x_2598_)) as u8;
                    if v_isSharedCheck_2607_ == 0 {
                        v___x_2601_ = v___x_2598_;
                        v_isShared_2602_ = v_isSharedCheck_2607_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2599_);
                        leanh::lean_dec(v___x_2598_);
                        v___x_2601_ = leanh::lean_box(0);
                        v_isShared_2602_ = v_isSharedCheck_2607_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2608_ = leanh::lean_ctor_get(v___x_2598_, 0);
                    v_isSharedCheck_2615_ = (!leanh::lean_is_exclusive(v___x_2598_)) as u8;
                    if v_isSharedCheck_2615_ == 0 {
                        v___x_2610_ = v___x_2598_;
                        v_isShared_2611_ = v_isSharedCheck_2615_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2608_);
                        leanh::lean_dec(v___x_2598_);
                        v___x_2610_ = leanh::lean_box(0);
                        v_isShared_2611_ = v_isSharedCheck_2615_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2603_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2603_, 0, v_a_2599_);
                if v_isShared_2602_ == 0 {
                    leanh::lean_ctor_set(v___x_2601_, 0, v___x_2603_);
                    v___x_2605_ = v___x_2601_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2606_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2606_, 0, v___x_2603_);
                    v___x_2605_ = v_reuseFailAlloc_2606_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2605_;
            }
            4 => {
                if v_isShared_2611_ == 0 {
                    v___x_2613_ = v___x_2610_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2614_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
                    v___x_2613_ = v_reuseFailAlloc_2614_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2613_;
            }
            6 => {
                v___x_2621_ = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2;
                leanh::lean_inc(v_name_2617_);
                v___x_2622_ = l_Lean_Syntax_isOfKind(v_name_2617_, v___x_2621_);
                if v___x_2622_ == 0 {
                    leanh::lean_dec(v_name_2617_);
                    leanh::lean_dec(v_expected_2577_);
                    v___x_2623_ = leanh::lean_box(0);
                    if v_isShared_2620_ == 0 {
                        leanh::lean_ctor_set(v___x_2619_, 0, v___x_2623_);
                        v___x_2625_ = v___x_2619_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2626_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2626_, 0, v___x_2623_);
                        v___x_2625_ = v_reuseFailAlloc_2626_;
                        state = 7;
                        continue;
                    }
                } else {
                    v___x_2627_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2628_ = l_Lean_Syntax_getArg(v_name_2617_, v___x_2627_);
                    leanh::lean_dec(v_name_2617_);
                    v___x_2629_ = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4;
                    leanh::lean_inc(v___x_2628_);
                    v___x_2630_ = l_Lean_Syntax_isOfKind(v___x_2628_, v___x_2629_);
                    if v___x_2630_ == 0 {
                        leanh::lean_dec(v___x_2628_);
                        leanh::lean_dec(v_expected_2577_);
                        v___x_2631_ = leanh::lean_box(0);
                        if v_isShared_2620_ == 0 {
                            leanh::lean_ctor_set(v___x_2619_, 0, v___x_2631_);
                            v___x_2633_ = v___x_2619_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_2634_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2634_, 0, v___x_2631_);
                            v___x_2633_ = v_reuseFailAlloc_2634_;
                            state = 8;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2619_);
                        v_t_2588_ = v___x_2628_;
                        v___y_2589_ = v_a_2578_;
                        v___y_2590_ = v_a_2579_;
                        v___y_2591_ = v_a_2580_;
                        v___y_2592_ = v_a_2581_;
                        v___y_2593_ = v_a_2582_;
                        v___y_2594_ = v_a_2583_;
                        v___y_2595_ = v_a_2584_;
                        v___y_2596_ = v_a_2585_;
                        state = 1;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_2625_;
            }
            8 => {
                return v___x_2633_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___boxed(
    mut v_pat_2638_: *mut leanh::LeanObject,
    mut v_expected_2639_: *mut leanh::LeanObject,
    mut v_a_2640_: *mut leanh::LeanObject,
    mut v_a_2641_: *mut leanh::LeanObject,
    mut v_a_2642_: *mut leanh::LeanObject,
    mut v_a_2643_: *mut leanh::LeanObject,
    mut v_a_2644_: *mut leanh::LeanObject,
    mut v_a_2645_: *mut leanh::LeanObject,
    mut v_a_2646_: *mut leanh::LeanObject,
    mut v_a_2647_: *mut leanh::LeanObject,
    mut v_a_2648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2649_ = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm(
        v_pat_2638_,
        v_expected_2639_,
        v_a_2640_,
        v_a_2641_,
        v_a_2642_,
        v_a_2643_,
        v_a_2644_,
        v_a_2645_,
        v_a_2646_,
        v_a_2647_,
    );
    leanh::lean_dec(v_a_2647_);
    leanh::lean_dec_ref(v_a_2646_);
    leanh::lean_dec(v_a_2645_);
    leanh::lean_dec_ref(v_a_2644_);
    leanh::lean_dec(v_a_2643_);
    leanh::lean_dec_ref(v_a_2642_);
    leanh::lean_dec(v_a_2641_);
    leanh::lean_dec_ref(v_a_2640_);
    return v_res_2649_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2650_ = leanh::lean_box(0);
    v___x_2651_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_2652_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2652_, 0, v___x_2651_);
    leanh::lean_ctor_set(v___x_2652_, 1, v___x_2650_);
    return v___x_2652_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2654_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg___closed__0);
    v___x_2655_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2655_, 0, v___x_2654_);
    return v___x_2655_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg___boxed(
    mut v___y_2656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2657_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg();
    return v_res_2657_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0(
    mut v_00_u03b1_2658_: *mut leanh::LeanObject,
    mut v___y_2659_: *mut leanh::LeanObject,
    mut v___y_2660_: *mut leanh::LeanObject,
    mut v___y_2661_: *mut leanh::LeanObject,
    mut v___y_2662_: *mut leanh::LeanObject,
    mut v___y_2663_: *mut leanh::LeanObject,
    mut v___y_2664_: *mut leanh::LeanObject,
    mut v___y_2665_: *mut leanh::LeanObject,
    mut v___y_2666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2668_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg();
    return v___x_2668_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___boxed(
    mut v_00_u03b1_2669_: *mut leanh::LeanObject,
    mut v___y_2670_: *mut leanh::LeanObject,
    mut v___y_2671_: *mut leanh::LeanObject,
    mut v___y_2672_: *mut leanh::LeanObject,
    mut v___y_2673_: *mut leanh::LeanObject,
    mut v___y_2674_: *mut leanh::LeanObject,
    mut v___y_2675_: *mut leanh::LeanObject,
    mut v___y_2676_: *mut leanh::LeanObject,
    mut v___y_2677_: *mut leanh::LeanObject,
    mut v___y_2678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2679_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0(v_00_u03b1_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
    leanh::lean_dec(v___y_2677_);
    leanh::lean_dec_ref(v___y_2676_);
    leanh::lean_dec(v___y_2675_);
    leanh::lean_dec_ref(v___y_2674_);
    leanh::lean_dec(v___y_2673_);
    leanh::lean_dec_ref(v___y_2672_);
    leanh::lean_dec(v___y_2671_);
    leanh::lean_dec_ref(v___y_2670_);
    return v_res_2679_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___lam__0(
    mut v___x_2680_: *mut leanh::LeanObject,
    mut v_00___2681_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: u8 = 0;
    v___x_2682_ = leanh::lean_unsigned_to_nat(3);
    v___x_2683_ = lean_array_get_size(v___x_2680_);
    v___x_2684_ = lean_nat_dec_le(v___x_2682_, v___x_2683_);
    return v___x_2684_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___lam__0___boxed(
    mut v___x_2685_: *mut leanh::LeanObject,
    mut v_00___2686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2687_: u8 = 0;
    let mut v_r_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2687_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___lam__0(v___x_2685_, v_00___2686_);
    leanh::lean_dec_ref(v___x_2685_);
    v_r_2688_ = leanh::lean_box((v_res_2687_) as usize);
    return v_r_2688_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__2(
    mut v_a_2689_: *mut leanh::LeanObject,
    mut v_a_2690_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2696_: u8 = 0;
    let mut v___x_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2702_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_2689_) == 0 {
                    v___x_2691_ = l_List_reverse___redArg(v_a_2690_);
                    return v___x_2691_;
                } else {
                    v_head_2692_ = leanh::lean_ctor_get(v_a_2689_, 0);
                    v_tail_2693_ = leanh::lean_ctor_get(v_a_2689_, 1);
                    v_isSharedCheck_2702_ = (!leanh::lean_is_exclusive(v_a_2689_)) as u8;
                    if v_isSharedCheck_2702_ == 0 {
                        v___x_2695_ = v_a_2689_;
                        v_isShared_2696_ = v_isSharedCheck_2702_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2693_);
                        leanh::lean_inc(v_head_2692_);
                        leanh::lean_dec(v_a_2689_);
                        v___x_2695_ = leanh::lean_box(0);
                        v_isShared_2696_ = v_isSharedCheck_2702_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2697_ = l_Lean_MessageData_ofExpr(v_head_2692_);
                if v_isShared_2696_ == 0 {
                    leanh::lean_ctor_set(v___x_2695_, 1, v_a_2690_);
                    leanh::lean_ctor_set(v___x_2695_, 0, v___x_2697_);
                    v___x_2699_ = v___x_2695_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2701_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2697_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2701_, 1, v_a_2690_);
                    v___x_2699_ = v_reuseFailAlloc_2701_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2689_ = v_tail_2693_;
                v_a_2690_ = v___x_2699_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1_spec__1(
    mut v_msgData_2703_: *mut leanh::LeanObject,
    mut v___y_2704_: *mut leanh::LeanObject,
    mut v___y_2705_: *mut leanh::LeanObject,
    mut v___y_2706_: *mut leanh::LeanObject,
    mut v___y_2707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2709_ = lean_st_ref_get(v___y_2707_);
    v_env_2710_ = leanh::lean_ctor_get(v___x_2709_, 0);
    leanh::lean_inc_ref(v_env_2710_);
    leanh::lean_dec(v___x_2709_);
    v___x_2711_ = lean_st_ref_get(v___y_2705_);
    v_mctx_2712_ = leanh::lean_ctor_get(v___x_2711_, 0);
    leanh::lean_inc_ref(v_mctx_2712_);
    leanh::lean_dec(v___x_2711_);
    v_lctx_2713_ = leanh::lean_ctor_get(v___y_2704_, 2);
    v_options_2714_ = leanh::lean_ctor_get(v___y_2706_, 2);
    leanh::lean_inc_ref(v_options_2714_);
    leanh::lean_inc_ref(v_lctx_2713_);
    v___x_2715_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2715_, 0, v_env_2710_);
    leanh::lean_ctor_set(v___x_2715_, 1, v_mctx_2712_);
    leanh::lean_ctor_set(v___x_2715_, 2, v_lctx_2713_);
    leanh::lean_ctor_set(v___x_2715_, 3, v_options_2714_);
    v___x_2716_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2716_, 0, v___x_2715_);
    leanh::lean_ctor_set(v___x_2716_, 1, v_msgData_2703_);
    v___x_2717_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2717_, 0, v___x_2716_);
    return v___x_2717_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1_spec__1___boxed(
    mut v_msgData_2718_: *mut leanh::LeanObject,
    mut v___y_2719_: *mut leanh::LeanObject,
    mut v___y_2720_: *mut leanh::LeanObject,
    mut v___y_2721_: *mut leanh::LeanObject,
    mut v___y_2722_: *mut leanh::LeanObject,
    mut v___y_2723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2724_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1_spec__1(v_msgData_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
    leanh::lean_dec(v___y_2722_);
    leanh::lean_dec_ref(v___y_2721_);
    leanh::lean_dec(v___y_2720_);
    leanh::lean_dec_ref(v___y_2719_);
    return v_res_2724_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg(
    mut v_msg_2725_: *mut leanh::LeanObject,
    mut v___y_2726_: *mut leanh::LeanObject,
    mut v___y_2727_: *mut leanh::LeanObject,
    mut v___y_2728_: *mut leanh::LeanObject,
    mut v___y_2729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2736_: u8 = 0;
    let mut v___x_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2741_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2731_ = leanh::lean_ctor_get(v___y_2728_, 5);
                v___x_2732_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1_spec__1(v_msg_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
                v_a_2733_ = leanh::lean_ctor_get(v___x_2732_, 0);
                v_isSharedCheck_2741_ = (!leanh::lean_is_exclusive(v___x_2732_)) as u8;
                if v_isSharedCheck_2741_ == 0 {
                    v___x_2735_ = v___x_2732_;
                    v_isShared_2736_ = v_isSharedCheck_2741_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2733_);
                    leanh::lean_dec(v___x_2732_);
                    v___x_2735_ = leanh::lean_box(0);
                    v_isShared_2736_ = v_isSharedCheck_2741_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_2731_);
                v___x_2737_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2737_, 0, v_ref_2731_);
                leanh::lean_ctor_set(v___x_2737_, 1, v_a_2733_);
                if v_isShared_2736_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2735_, 1);
                    leanh::lean_ctor_set(v___x_2735_, 0, v___x_2737_);
                    v___x_2739_ = v___x_2735_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2740_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2737_);
                    v___x_2739_ = v_reuseFailAlloc_2740_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2739_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg___boxed(
    mut v_msg_2742_: *mut leanh::LeanObject,
    mut v___y_2743_: *mut leanh::LeanObject,
    mut v___y_2744_: *mut leanh::LeanObject,
    mut v___y_2745_: *mut leanh::LeanObject,
    mut v___y_2746_: *mut leanh::LeanObject,
    mut v___y_2747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2748_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg(
            v_msg_2742_,
            v___y_2743_,
            v___y_2744_,
            v___y_2745_,
            v___y_2746_,
        );
    leanh::lean_dec(v___y_2746_);
    leanh::lean_dec_ref(v___y_2745_);
    leanh::lean_dec(v___y_2744_);
    leanh::lean_dec_ref(v___y_2743_);
    return v_res_2748_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__0()
-> f64 {
    let mut v___x_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: f64 = 0.0;
    v___x_2749_ = leanh::lean_unsigned_to_nat(0);
    v___x_2750_ = lean_float_of_nat(v___x_2749_);
    return v___x_2750_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg(
    mut v_cls_2754_: *mut leanh::LeanObject,
    mut v_msg_2755_: *mut leanh::LeanObject,
    mut v___y_2756_: *mut leanh::LeanObject,
    mut v___y_2757_: *mut leanh::LeanObject,
    mut v___y_2758_: *mut leanh::LeanObject,
    mut v___y_2759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2766_: u8 = 0;
    let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2779_: u8 = 0;
    let mut v_tid_2780_: u64 = 0;
    let mut v_traces_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2784_: u8 = 0;
    let mut v___x_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: f64 = 0.0;
    let mut v___x_2787_: u8 = 0;
    let mut v___x_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2805_: u8 = 0;
    let mut v_isSharedCheck_2806_: u8 = 0;
    let mut v_isSharedCheck_2807_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2761_ = leanh::lean_ctor_get(v___y_2758_, 5);
                v___x_2762_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1_spec__1(v_msg_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
                v_a_2763_ = leanh::lean_ctor_get(v___x_2762_, 0);
                v_isSharedCheck_2807_ = (!leanh::lean_is_exclusive(v___x_2762_)) as u8;
                if v_isSharedCheck_2807_ == 0 {
                    v___x_2765_ = v___x_2762_;
                    v_isShared_2766_ = v_isSharedCheck_2807_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2763_);
                    leanh::lean_dec(v___x_2762_);
                    v___x_2765_ = leanh::lean_box(0);
                    v_isShared_2766_ = v_isSharedCheck_2807_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2767_ = lean_st_ref_take(v___y_2759_);
                v_traceState_2768_ = leanh::lean_ctor_get(v___x_2767_, 4);
                v_env_2769_ = leanh::lean_ctor_get(v___x_2767_, 0);
                v_nextMacroScope_2770_ = leanh::lean_ctor_get(v___x_2767_, 1);
                v_ngen_2771_ = leanh::lean_ctor_get(v___x_2767_, 2);
                v_auxDeclNGen_2772_ = leanh::lean_ctor_get(v___x_2767_, 3);
                v_cache_2773_ = leanh::lean_ctor_get(v___x_2767_, 5);
                v_messages_2774_ = leanh::lean_ctor_get(v___x_2767_, 6);
                v_infoState_2775_ = leanh::lean_ctor_get(v___x_2767_, 7);
                v_snapshotTasks_2776_ = leanh::lean_ctor_get(v___x_2767_, 8);
                v_isSharedCheck_2806_ = (!leanh::lean_is_exclusive(v___x_2767_)) as u8;
                if v_isSharedCheck_2806_ == 0 {
                    v___x_2778_ = v___x_2767_;
                    v_isShared_2779_ = v_isSharedCheck_2806_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2776_);
                    leanh::lean_inc(v_infoState_2775_);
                    leanh::lean_inc(v_messages_2774_);
                    leanh::lean_inc(v_cache_2773_);
                    leanh::lean_inc(v_traceState_2768_);
                    leanh::lean_inc(v_auxDeclNGen_2772_);
                    leanh::lean_inc(v_ngen_2771_);
                    leanh::lean_inc(v_nextMacroScope_2770_);
                    leanh::lean_inc(v_env_2769_);
                    leanh::lean_dec(v___x_2767_);
                    v___x_2778_ = leanh::lean_box(0);
                    v_isShared_2779_ = v_isSharedCheck_2806_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2780_ = leanh::lean_ctor_get_uint64(
                    v_traceState_2768_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_2781_ = leanh::lean_ctor_get(v_traceState_2768_, 0);
                v_isSharedCheck_2805_ =
                    (!leanh::lean_is_exclusive(v_traceState_2768_)) as u8;
                if v_isSharedCheck_2805_ == 0 {
                    v___x_2783_ = v_traceState_2768_;
                    v_isShared_2784_ = v_isSharedCheck_2805_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_2781_);
                    leanh::lean_dec(v_traceState_2768_);
                    v___x_2783_ = leanh::lean_box(0);
                    v_isShared_2784_ = v_isSharedCheck_2805_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2785_ = leanh::lean_box(0);
                v___x_2786_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__0);
                v___x_2787_ = 0;
                v___x_2788_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__1;
                v___x_2789_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_2789_, 0, v_cls_2754_);
                leanh::lean_ctor_set(v___x_2789_, 1, v___x_2785_);
                leanh::lean_ctor_set(v___x_2789_, 2, v___x_2788_);
                leanh::lean_ctor_set_float(
                    v___x_2789_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_2786_,
                );
                leanh::lean_ctor_set_float(
                    v___x_2789_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_2786_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2789_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_2787_,
                );
                v___x_2790_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__2;
                v___x_2791_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2791_, 0, v___x_2789_);
                leanh::lean_ctor_set(v___x_2791_, 1, v_a_2763_);
                leanh::lean_ctor_set(v___x_2791_, 2, v___x_2790_);
                leanh::lean_inc(v_ref_2761_);
                v___x_2792_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2792_, 0, v_ref_2761_);
                leanh::lean_ctor_set(v___x_2792_, 1, v___x_2791_);
                v___x_2793_ = l_Lean_PersistentArray_push___redArg(v_traces_2781_, v___x_2792_);
                if v_isShared_2784_ == 0 {
                    leanh::lean_ctor_set(v___x_2783_, 0, v___x_2793_);
                    v___x_2795_ = v___x_2783_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2804_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2793_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2804_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_2780_,
                    );
                    v___x_2795_ = v_reuseFailAlloc_2804_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2779_ == 0 {
                    leanh::lean_ctor_set(v___x_2778_, 4, v___x_2795_);
                    v___x_2797_ = v___x_2778_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2803_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_env_2769_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2803_, 1, v_nextMacroScope_2770_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2803_, 2, v_ngen_2771_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2803_, 3, v_auxDeclNGen_2772_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2803_, 4, v___x_2795_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2803_, 5, v_cache_2773_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2803_, 6, v_messages_2774_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2803_, 7, v_infoState_2775_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2803_, 8, v_snapshotTasks_2776_);
                    v___x_2797_ = v_reuseFailAlloc_2803_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2798_ = lean_st_ref_set(v___y_2759_, v___x_2797_);
                v___x_2799_ = leanh::lean_box(0);
                if v_isShared_2766_ == 0 {
                    leanh::lean_ctor_set(v___x_2765_, 0, v___x_2799_);
                    v___x_2801_ = v___x_2765_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2802_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2802_, 0, v___x_2799_);
                    v___x_2801_ = v_reuseFailAlloc_2802_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2801_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___boxed(
    mut v_cls_2808_: *mut leanh::LeanObject,
    mut v_msg_2809_: *mut leanh::LeanObject,
    mut v___y_2810_: *mut leanh::LeanObject,
    mut v___y_2811_: *mut leanh::LeanObject,
    mut v___y_2812_: *mut leanh::LeanObject,
    mut v___y_2813_: *mut leanh::LeanObject,
    mut v___y_2814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2815_ =
        l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg(
            v_cls_2808_,
            v_msg_2809_,
            v___y_2810_,
            v___y_2811_,
            v___y_2812_,
            v___y_2813_,
        );
    leanh::lean_dec(v___y_2813_);
    leanh::lean_dec_ref(v___y_2812_);
    leanh::lean_dec(v___y_2811_);
    leanh::lean_dec_ref(v___y_2810_);
    return v_res_2815_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg(
    mut v_msg_2816_: *mut leanh::LeanObject,
    mut v___y_2817_: *mut leanh::LeanObject,
    mut v___y_2818_: *mut leanh::LeanObject,
    mut v___y_2819_: *mut leanh::LeanObject,
    mut v___y_2820_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2827_: u8 = 0;
    let mut v___x_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2832_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2822_ = leanh::lean_ctor_get(v___y_2819_, 5);
                v___x_2823_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1_spec__1(v_msg_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
                v_a_2824_ = leanh::lean_ctor_get(v___x_2823_, 0);
                v_isSharedCheck_2832_ = (!leanh::lean_is_exclusive(v___x_2823_)) as u8;
                if v_isSharedCheck_2832_ == 0 {
                    v___x_2826_ = v___x_2823_;
                    v_isShared_2827_ = v_isSharedCheck_2832_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2824_);
                    leanh::lean_dec(v___x_2823_);
                    v___x_2826_ = leanh::lean_box(0);
                    v_isShared_2827_ = v_isSharedCheck_2832_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_2822_);
                v___x_2828_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2828_, 0, v_ref_2822_);
                leanh::lean_ctor_set(v___x_2828_, 1, v_a_2824_);
                if v_isShared_2827_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2826_, 1);
                    leanh::lean_ctor_set(v___x_2826_, 0, v___x_2828_);
                    v___x_2830_ = v___x_2826_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2831_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2831_, 0, v___x_2828_);
                    v___x_2830_ = v_reuseFailAlloc_2831_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2830_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg___boxed(
    mut v_msg_2833_: *mut leanh::LeanObject,
    mut v___y_2834_: *mut leanh::LeanObject,
    mut v___y_2835_: *mut leanh::LeanObject,
    mut v___y_2836_: *mut leanh::LeanObject,
    mut v___y_2837_: *mut leanh::LeanObject,
    mut v___y_2838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2839_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg(
            v_msg_2833_,
            v___y_2834_,
            v___y_2835_,
            v___y_2836_,
            v___y_2837_,
        );
    leanh::lean_dec(v___y_2837_);
    leanh::lean_dec_ref(v___y_2836_);
    leanh::lean_dec(v___y_2835_);
    leanh::lean_dec_ref(v___y_2834_);
    return v_res_2839_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2840_ = leanh::lean_box(0);
    v_dummy_2841_ = l_Lean_Expr_sort___override(v___x_2840_);
    return v_dummy_2841_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2843_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__1;
    v___x_2844_ = l_Lean_stringToMessageData(v___x_2843_);
    return v___x_2844_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2847_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__4;
    v___x_2848_ = l_Lean_stringToMessageData(v___x_2847_);
    return v___x_2848_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2868_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15;
    v___x_2869_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17;
    v___x_2870_ = l_Lean_Name_append(v___x_2869_, v___x_2868_);
    return v___x_2870_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2872_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__19;
    v___x_2873_ = l_Lean_stringToMessageData(v___x_2872_);
    return v___x_2873_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2875_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__21;
    v___x_2876_ = l_Lean_stringToMessageData(v___x_2875_);
    return v___x_2876_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2878_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__23;
    v___x_2879_ = l_Lean_stringToMessageData(v___x_2878_);
    return v___x_2879_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26()
-> *mut leanh::LeanObject {
    let mut v___x_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2881_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__25;
    v___x_2882_ = l_Lean_stringToMessageData(v___x_2881_);
    return v___x_2882_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__28()
-> *mut leanh::LeanObject {
    let mut v___x_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2884_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__27;
    v___x_2885_ = l_Lean_stringToMessageData(v___x_2884_);
    return v___x_2885_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__30()
-> *mut leanh::LeanObject {
    let mut v___x_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2887_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__29;
    v___x_2888_ = l_Lean_stringToMessageData(v___x_2887_);
    return v___x_2888_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___boxed(
    mut v_goal_2889_: *mut leanh::LeanObject,
    mut v_pat_2890_: *mut leanh::LeanObject,
    mut v_k_2891_: *mut leanh::LeanObject,
    mut v_a_2892_: *mut leanh::LeanObject,
    mut v_a_2893_: *mut leanh::LeanObject,
    mut v_a_2894_: *mut leanh::LeanObject,
    mut v_a_2895_: *mut leanh::LeanObject,
    mut v_a_2896_: *mut leanh::LeanObject,
    mut v_a_2897_: *mut leanh::LeanObject,
    mut v_a_2898_: *mut leanh::LeanObject,
    mut v_a_2899_: *mut leanh::LeanObject,
    mut v_a_2900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2901_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(
        v_goal_2889_,
        v_pat_2890_,
        v_k_2891_,
        v_a_2892_,
        v_a_2893_,
        v_a_2894_,
        v_a_2895_,
        v_a_2896_,
        v_a_2897_,
        v_a_2898_,
        v_a_2899_,
    );
    leanh::lean_dec(v_a_2899_);
    leanh::lean_dec_ref(v_a_2898_);
    leanh::lean_dec(v_a_2897_);
    leanh::lean_dec_ref(v_a_2896_);
    leanh::lean_dec(v_a_2895_);
    leanh::lean_dec_ref(v_a_2894_);
    leanh::lean_dec(v_a_2893_);
    leanh::lean_dec_ref(v_a_2892_);
    return v_res_2901_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(
    mut v_goal_2902_: *mut leanh::LeanObject,
    mut v_pat_2903_: *mut leanh::LeanObject,
    mut v_k_2904_: *mut leanh::LeanObject,
    mut v_a_2905_: *mut leanh::LeanObject,
    mut v_a_2906_: *mut leanh::LeanObject,
    mut v_a_2907_: *mut leanh::LeanObject,
    mut v_a_2908_: *mut leanh::LeanObject,
    mut v_a_2909_: *mut leanh::LeanObject,
    mut v_a_2910_: *mut leanh::LeanObject,
    mut v_a_2911_: *mut leanh::LeanObject,
    mut v_a_2912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2917_: u8 = 0;
    let mut v___x_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: u8 = 0;
    let mut v___x_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: u8 = 0;
    let mut v___x_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2940_: u8 = 0;
    let mut v___x_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2943_: u8 = 0;
    let mut v___x_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2952_: u8 = 0;
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2956_: u8 = 0;
    let mut v_isSharedCheck_2957_: u8 = 0;
    let mut v_unused_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: u8 = 0;
    let mut v___x_2960_: u8 = 0;
    let mut v_reuseFailAlloc_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2965_: u8 = 0;
    let mut v___x_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2969_: u8 = 0;
    let mut v_isSharedCheck_2970_: u8 = 0;
    let mut v_args_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2974_: u8 = 0;
    let mut v___x_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2982_: u8 = 0;
    let mut v_u_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2989_: u8 = 0;
    let mut v___x_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2995_: u8 = 0;
    let mut v_inheritedTraceOptions_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2997_: u8 = 0;
    let mut v___x_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3017_: u8 = 0;
    let mut v___x_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3050_: u8 = 0;
    let mut v___x_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3063_: u8 = 0;
    let mut v_a_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3067_: u8 = 0;
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3071_: u8 = 0;
    let mut v_reuseFailAlloc_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3079_: u8 = 0;
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3083_: u8 = 0;
    let mut v_reuseFailAlloc_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3097_: u8 = 0;
    let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: u8 = 0;
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: u8 = 0;
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3115_: u8 = 0;
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3126_: u8 = 0;
    let mut v___x_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3136_: u8 = 0;
    let mut v_reuseFailAlloc_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3138_: u8 = 0;
    let mut v___y_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: u8 = 0;
    let mut v___x_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: u8 = 0;
    let mut v___x_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: u8 = 0;
    let mut v___x_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3172_: u8 = 0;
    let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3176_: u8 = 0;
    let mut v_isSharedCheck_3177_: u8 = 0;
    let mut v_isSharedCheck_3178_: u8 = 0;
    let mut v_isSharedCheck_3179_: u8 = 0;
    let mut v_unused_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3181_: u8 = 0;
    let mut v_h_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: u8 = 0;
    let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3191_: u8 = 0;
    let mut v_val_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3203_: u8 = 0;
    let mut v_a_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3207_: u8 = 0;
    let mut v___x_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3211_: u8 = 0;
    let mut v___x_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: u8 = 0;
    let mut v___x_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3220_: u8 = 0;
    let mut v_val_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3232_: u8 = 0;
    let mut v_a_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3236_: u8 = 0;
    let mut v___x_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3240_: u8 = 0;
    let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3245_: u8 = 0;
    let mut v_val_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3257_: u8 = 0;
    let mut v_a_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3261_: u8 = 0;
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3265_: u8 = 0;
    let mut v_name_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_pat_2903_) {
                0 => {
                    v_name_2914_ = leanh::lean_ctor_get(v_pat_2903_, 0);
                    v_isSharedCheck_2970_ = (!leanh::lean_is_exclusive(v_pat_2903_)) as u8;
                    if v_isSharedCheck_2970_ == 0 {
                        v___x_2916_ = v_pat_2903_;
                        v_isShared_2917_ = v_isSharedCheck_2970_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_name_2914_);
                        leanh::lean_dec(v_pat_2903_);
                        v___x_2916_ = leanh::lean_box(0);
                        v_isShared_2917_ = v_isSharedCheck_2970_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_args_2971_ = leanh::lean_ctor_get(v_pat_2903_, 0);
                    v_isSharedCheck_3181_ = (!leanh::lean_is_exclusive(v_pat_2903_)) as u8;
                    if v_isSharedCheck_3181_ == 0 {
                        v___x_2973_ = v_pat_2903_;
                        v_isShared_2974_ = v_isSharedCheck_3181_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_args_2971_);
                        leanh::lean_dec(v_pat_2903_);
                        v___x_2973_ = leanh::lean_box(0);
                        v_isShared_2974_ = v_isSharedCheck_3181_;
                        state = 12;
                        continue;
                    }
                }
                2 => {
                    leanh::lean_dec_ref(v_k_2904_);
                    v_h_3182_ = leanh::lean_ctor_get(v_pat_2903_, 0);
                    leanh::lean_inc(v_h_3182_);
                    leanh::lean_dec_ref_known(v_pat_2903_, 1);
                    v___x_3183_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exactPure(
                        v_goal_2902_,
                        v_h_3182_,
                        v_a_2905_,
                        v_a_2906_,
                        v_a_2907_,
                        v_a_2908_,
                        v_a_2909_,
                        v_a_2910_,
                        v_a_2911_,
                        v_a_2912_,
                    );
                    return v___x_3183_;
                }
                3 => {
                    leanh::lean_dec_ref(v_k_2904_);
                    v_h_3184_ = leanh::lean_ctor_get(v_pat_2903_, 0);
                    leanh::lean_inc_n(v_h_3184_, 2);
                    leanh::lean_dec_ref_known(v_pat_2903_, 1);
                    v___x_3185_ = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2;
                    v___x_3186_ = l_Lean_Syntax_isOfKind(v_h_3184_, v___x_3185_);
                    if v___x_3186_ == 0 {
                        leanh::lean_dec(v_h_3184_);
                        leanh::lean_inc_ref(v_goal_2902_);
                        v___x_3187_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption(
                            v_goal_2902_,
                            v_a_2909_,
                            v_a_2910_,
                            v_a_2911_,
                            v_a_2912_,
                        );
                        if leanh::lean_obj_tag(v___x_3187_) == 0 {
                            v_a_3188_ = leanh::lean_ctor_get(v___x_3187_, 0);
                            v_isSharedCheck_3203_ =
                                (!leanh::lean_is_exclusive(v___x_3187_)) as u8;
                            if v_isSharedCheck_3203_ == 0 {
                                v___x_3190_ = v___x_3187_;
                                v_isShared_3191_ = v_isSharedCheck_3203_;
                                state = 35;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3188_);
                                leanh::lean_dec(v___x_3187_);
                                v___x_3190_ = leanh::lean_box(0);
                                v_isShared_3191_ = v_isSharedCheck_3203_;
                                state = 35;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_goal_2902_);
                            v_a_3204_ = leanh::lean_ctor_get(v___x_3187_, 0);
                            v_isSharedCheck_3211_ =
                                (!leanh::lean_is_exclusive(v___x_3187_)) as u8;
                            if v_isSharedCheck_3211_ == 0 {
                                v___x_3206_ = v___x_3187_;
                                v_isShared_3207_ = v_isSharedCheck_3211_;
                                state = 37;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3204_);
                                leanh::lean_dec(v___x_3187_);
                                v___x_3206_ = leanh::lean_box(0);
                                v_isShared_3207_ = v_isSharedCheck_3211_;
                                state = 37;
                                continue;
                            }
                        }
                    } else {
                        v___x_3212_ = leanh::lean_unsigned_to_nat(0);
                        v_name_3213_ = l_Lean_Syntax_getArg(v_h_3184_, v___x_3212_);
                        leanh::lean_dec(v_h_3184_);
                        v___x_3214_ = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4;
                        leanh::lean_inc(v_name_3213_);
                        v___x_3215_ = l_Lean_Syntax_isOfKind(v_name_3213_, v___x_3214_);
                        if v___x_3215_ == 0 {
                            leanh::lean_dec(v_name_3213_);
                            leanh::lean_inc_ref(v_goal_2902_);
                            v___x_3216_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_assumption(
                                v_goal_2902_,
                                v_a_2909_,
                                v_a_2910_,
                                v_a_2911_,
                                v_a_2912_,
                            );
                            if leanh::lean_obj_tag(v___x_3216_) == 0 {
                                v_a_3217_ = leanh::lean_ctor_get(v___x_3216_, 0);
                                v_isSharedCheck_3232_ =
                                    (!leanh::lean_is_exclusive(v___x_3216_)) as u8;
                                if v_isSharedCheck_3232_ == 0 {
                                    v___x_3219_ = v___x_3216_;
                                    v_isShared_3220_ = v_isSharedCheck_3232_;
                                    state = 39;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3217_);
                                    leanh::lean_dec(v___x_3216_);
                                    v___x_3219_ = leanh::lean_box(0);
                                    v_isShared_3220_ = v_isSharedCheck_3232_;
                                    state = 39;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v_goal_2902_);
                                v_a_3233_ = leanh::lean_ctor_get(v___x_3216_, 0);
                                v_isSharedCheck_3240_ =
                                    (!leanh::lean_is_exclusive(v___x_3216_)) as u8;
                                if v_isSharedCheck_3240_ == 0 {
                                    v___x_3235_ = v___x_3216_;
                                    v_isShared_3236_ = v_isSharedCheck_3240_;
                                    state = 41;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3233_);
                                    leanh::lean_dec(v___x_3216_);
                                    v___x_3235_ = leanh::lean_box(0);
                                    v_isShared_3236_ = v_isSharedCheck_3240_;
                                    state = 41;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_inc(v_name_3213_);
                            v___x_3241_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_exact(
                                v_goal_2902_,
                                v_name_3213_,
                                v_a_2909_,
                                v_a_2910_,
                                v_a_2911_,
                                v_a_2912_,
                            );
                            if leanh::lean_obj_tag(v___x_3241_) == 0 {
                                v_a_3242_ = leanh::lean_ctor_get(v___x_3241_, 0);
                                v_isSharedCheck_3257_ =
                                    (!leanh::lean_is_exclusive(v___x_3241_)) as u8;
                                if v_isSharedCheck_3257_ == 0 {
                                    v___x_3244_ = v___x_3241_;
                                    v_isShared_3245_ = v_isSharedCheck_3257_;
                                    state = 43;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3242_);
                                    leanh::lean_dec(v___x_3241_);
                                    v___x_3244_ = leanh::lean_box(0);
                                    v_isShared_3245_ = v_isSharedCheck_3257_;
                                    state = 43;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_name_3213_);
                                v_a_3258_ = leanh::lean_ctor_get(v___x_3241_, 0);
                                v_isSharedCheck_3265_ =
                                    (!leanh::lean_is_exclusive(v___x_3241_)) as u8;
                                if v_isSharedCheck_3265_ == 0 {
                                    v___x_3260_ = v___x_3241_;
                                    v_isShared_3261_ = v_isSharedCheck_3265_;
                                    state = 45;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3258_);
                                    leanh::lean_dec(v___x_3241_);
                                    v___x_3260_ = leanh::lean_box(0);
                                    v_isShared_3261_ = v_isSharedCheck_3265_;
                                    state = 45;
                                    continue;
                                }
                            }
                        }
                    }
                }
                _ => {
                    v_name_3266_ = leanh::lean_ctor_get(v_pat_2903_, 0);
                    leanh::lean_inc(v_name_3266_);
                    leanh::lean_dec_ref_known(v_pat_2903_, 1);
                    leanh::lean_inc(v_a_2912_);
                    leanh::lean_inc_ref(v_a_2911_);
                    leanh::lean_inc(v_a_2910_);
                    leanh::lean_inc_ref(v_a_2909_);
                    leanh::lean_inc(v_a_2908_);
                    leanh::lean_inc_ref(v_a_2907_);
                    leanh::lean_inc(v_a_2906_);
                    leanh::lean_inc_ref(v_a_2905_);
                    v___x_3267_ = leanh::lean_apply_11(
                        v_k_2904_,
                        v_goal_2902_,
                        v_name_3266_,
                        v_a_2905_,
                        v_a_2906_,
                        v_a_2907_,
                        v_a_2908_,
                        v_a_2909_,
                        v_a_2910_,
                        v_a_2911_,
                        v_a_2912_,
                        leanh::lean_box(0),
                    );
                    return v___x_3267_;
                }
            },
            1 => {
                v___x_2918_ = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2;
                leanh::lean_inc(v_name_2914_);
                v___x_2919_ = l_Lean_Syntax_isOfKind(v_name_2914_, v___x_2918_);
                if v___x_2919_ == 0 {
                    if v_isShared_2917_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2916_, 3);
                        v___x_2921_ = v___x_2916_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2923_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_name_2914_);
                        v___x_2921_ = v_reuseFailAlloc_2923_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2924_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2925_ = l_Lean_Syntax_getArg(v_name_2914_, v___x_2924_);
                    v___x_2926_ = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__4;
                    v___x_2927_ = l_Lean_Syntax_isOfKind(v___x_2925_, v___x_2926_);
                    if v___x_2927_ == 0 {
                        if v_isShared_2917_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_2916_, 3);
                            v___x_2929_ = v___x_2916_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2931_ =
                                leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_name_2914_);
                            v___x_2929_ = v_reuseFailAlloc_2931_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2932_ = l_Lean_Elab_Tactic_saveState___redArg(
                            v_a_2906_, v_a_2908_, v_a_2910_, v_a_2912_,
                        );
                        if leanh::lean_obj_tag(v___x_2932_) == 0 {
                            v_a_2933_ = leanh::lean_ctor_get(v___x_2932_, 0);
                            leanh::lean_inc(v_a_2933_);
                            leanh::lean_dec_ref_known(v___x_2932_, 1);
                            leanh::lean_inc(v_name_2914_);
                            if v_isShared_2917_ == 0 {
                                leanh::lean_ctor_set_tag(v___x_2916_, 2);
                                v___x_2935_ = v___x_2916_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_2961_ =
                                    leanh::lean_alloc_ctor(2, 1, (0) as u32);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2961_,
                                    0,
                                    v_name_2914_,
                                );
                                v___x_2935_ = v_reuseFailAlloc_2961_;
                                state = 4;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_2916_);
                            leanh::lean_dec(v_name_2914_);
                            leanh::lean_dec_ref(v_k_2904_);
                            leanh::lean_dec_ref(v_goal_2902_);
                            v_a_2962_ = leanh::lean_ctor_get(v___x_2932_, 0);
                            v_isSharedCheck_2969_ =
                                (!leanh::lean_is_exclusive(v___x_2932_)) as u8;
                            if v_isSharedCheck_2969_ == 0 {
                                v___x_2964_ = v___x_2932_;
                                v_isShared_2965_ = v_isSharedCheck_2969_;
                                state = 10;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2962_);
                                leanh::lean_dec(v___x_2932_);
                                v___x_2964_ = leanh::lean_box(0);
                                v_isShared_2965_ = v_isSharedCheck_2969_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                v_pat_2903_ = v___x_2921_;
                state = 0;
                continue;
            }
            3 => {
                v_pat_2903_ = v___x_2929_;
                state = 0;
                continue;
            }
            4 => {
                leanh::lean_inc_ref(v_k_2904_);
                leanh::lean_inc_ref(v_goal_2902_);
                v___x_2936_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___boxed as *mut core::ffi::c_void,
                    12,
                    3,
                );
                leanh::lean_closure_set(v___x_2936_, 0, v_goal_2902_);
                leanh::lean_closure_set(v___x_2936_, 1, v___x_2935_);
                leanh::lean_closure_set(v___x_2936_, 2, v_k_2904_);
                v___x_2937_ = l_Lean_Elab_Tactic_withoutRecover___redArg(
                    v___x_2936_,
                    v_a_2905_,
                    v_a_2906_,
                    v_a_2907_,
                    v_a_2908_,
                    v_a_2909_,
                    v_a_2910_,
                    v_a_2911_,
                    v_a_2912_,
                );
                if leanh::lean_obj_tag(v___x_2937_) == 0 {
                    leanh::lean_dec(v_a_2933_);
                    leanh::lean_dec(v_name_2914_);
                    leanh::lean_dec_ref(v_k_2904_);
                    leanh::lean_dec_ref(v_goal_2902_);
                    return v___x_2937_;
                } else {
                    v_a_2938_ = leanh::lean_ctor_get(v___x_2937_, 0);
                    leanh::lean_inc(v_a_2938_);
                    v___x_2959_ = l_Lean_Exception_isInterrupt(v_a_2938_);
                    if v___x_2959_ == 0 {
                        v___x_2960_ = l_Lean_Exception_isRuntime(v_a_2938_);
                        v___y_2940_ = v___x_2960_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_2938_);
                        v___y_2940_ = v___x_2959_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v___y_2940_ == 0 {
                    v_isSharedCheck_2957_ = (!leanh::lean_is_exclusive(v___x_2937_)) as u8;
                    if v_isSharedCheck_2957_ == 0 {
                        v_unused_2958_ = leanh::lean_ctor_get(v___x_2937_, 0);
                        leanh::lean_dec(v_unused_2958_);
                        v___x_2942_ = v___x_2937_;
                        v_isShared_2943_ = v_isSharedCheck_2957_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2937_);
                        v___x_2942_ = leanh::lean_box(0);
                        v_isShared_2943_ = v_isSharedCheck_2957_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_2933_);
                    leanh::lean_dec(v_name_2914_);
                    leanh::lean_dec_ref(v_k_2904_);
                    leanh::lean_dec_ref(v_goal_2902_);
                    return v___x_2937_;
                }
            }
            6 => {
                v___x_2944_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(
                    v_a_2933_,
                    v___y_2940_,
                    v_a_2906_,
                    v_a_2907_,
                    v_a_2908_,
                    v_a_2909_,
                    v_a_2910_,
                    v_a_2911_,
                    v_a_2912_,
                );
                if leanh::lean_obj_tag(v___x_2944_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2944_, 1);
                    if v_isShared_2943_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2942_, 3);
                        leanh::lean_ctor_set(v___x_2942_, 0, v_name_2914_);
                        v___x_2946_ = v___x_2942_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2948_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_name_2914_);
                        v___x_2946_ = v_reuseFailAlloc_2948_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2942_);
                    leanh::lean_dec(v_name_2914_);
                    leanh::lean_dec_ref(v_k_2904_);
                    leanh::lean_dec_ref(v_goal_2902_);
                    v_a_2949_ = leanh::lean_ctor_get(v___x_2944_, 0);
                    v_isSharedCheck_2956_ = (!leanh::lean_is_exclusive(v___x_2944_)) as u8;
                    if v_isSharedCheck_2956_ == 0 {
                        v___x_2951_ = v___x_2944_;
                        v_isShared_2952_ = v_isSharedCheck_2956_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2949_);
                        leanh::lean_dec(v___x_2944_);
                        v___x_2951_ = leanh::lean_box(0);
                        v_isShared_2952_ = v_isSharedCheck_2956_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                v_pat_2903_ = v___x_2946_;
                state = 0;
                continue;
            }
            8 => {
                if v_isShared_2952_ == 0 {
                    v___x_2954_ = v___x_2951_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2955_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
                    v___x_2954_ = v_reuseFailAlloc_2955_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2954_;
            }
            10 => {
                if v_isShared_2965_ == 0 {
                    v___x_2967_ = v___x_2964_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2968_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_a_2962_);
                    v___x_2967_ = v_reuseFailAlloc_2968_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2967_;
            }
            12 => {
                if leanh::lean_obj_tag(v_args_2971_) == 0 {
                    leanh::lean_del_object(v___x_2973_);
                    leanh::lean_dec_ref(v_k_2904_);
                    leanh::lean_dec_ref(v_goal_2902_);
                    v___x_2975_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg();
                    return v___x_2975_;
                } else {
                    v_tail_2976_ = leanh::lean_ctor_get(v_args_2971_, 1);
                    if leanh::lean_obj_tag(v_tail_2976_) == 0 {
                        leanh::lean_del_object(v___x_2973_);
                        v_head_2977_ = leanh::lean_ctor_get(v_args_2971_, 0);
                        leanh::lean_inc(v_head_2977_);
                        leanh::lean_dec_ref_known(v_args_2971_, 2);
                        v_pat_2903_ = v_head_2977_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2976_);
                        v_head_2979_ = leanh::lean_ctor_get(v_args_2971_, 0);
                        v_isSharedCheck_3179_ =
                            (!leanh::lean_is_exclusive(v_args_2971_)) as u8;
                        if v_isSharedCheck_3179_ == 0 {
                            v_unused_3180_ = leanh::lean_ctor_get(v_args_2971_, 1);
                            leanh::lean_dec(v_unused_3180_);
                            v___x_2981_ = v_args_2971_;
                            v_isShared_2982_ = v_isSharedCheck_3179_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_head_2979_);
                            leanh::lean_dec(v_args_2971_);
                            v___x_2981_ = leanh::lean_box(0);
                            v_isShared_2982_ = v_isSharedCheck_3179_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            13 => {
                v_u_2983_ = leanh::lean_ctor_get(v_goal_2902_, 0);
                v_00_u03c3s_2984_ = leanh::lean_ctor_get(v_goal_2902_, 1);
                v_hyps_2985_ = leanh::lean_ctor_get(v_goal_2902_, 2);
                v_target_2986_ = leanh::lean_ctor_get(v_goal_2902_, 3);
                v_isSharedCheck_3178_ = (!leanh::lean_is_exclusive(v_goal_2902_)) as u8;
                if v_isSharedCheck_3178_ == 0 {
                    v___x_2988_ = v_goal_2902_;
                    v_isShared_2989_ = v_isSharedCheck_3178_;
                    state = 14;
                    continue;
                } else {
                    leanh::lean_inc(v_target_2986_);
                    leanh::lean_inc(v_hyps_2985_);
                    leanh::lean_inc(v_00_u03c3s_2984_);
                    leanh::lean_inc(v_u_2983_);
                    leanh::lean_dec(v_goal_2902_);
                    v___x_2988_ = leanh::lean_box(0);
                    v_isShared_2989_ = v_isSharedCheck_3178_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_2990_ =
                    l_Lean_Meta_whnfR(v_target_2986_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
                if leanh::lean_obj_tag(v___x_2990_) == 0 {
                    v_options_2991_ = leanh::lean_ctor_get(v_a_2911_, 2);
                    v_a_2992_ = leanh::lean_ctor_get(v___x_2990_, 0);
                    v_isSharedCheck_3177_ = (!leanh::lean_is_exclusive(v___x_2990_)) as u8;
                    if v_isSharedCheck_3177_ == 0 {
                        v___x_2994_ = v___x_2990_;
                        v_isShared_2995_ = v_isSharedCheck_3177_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2992_);
                        leanh::lean_dec(v___x_2990_);
                        v___x_2994_ = leanh::lean_box(0);
                        v_isShared_2995_ = v_isSharedCheck_3177_;
                        state = 15;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2988_);
                    leanh::lean_dec_ref(v_hyps_2985_);
                    leanh::lean_dec_ref(v_00_u03c3s_2984_);
                    leanh::lean_dec(v_u_2983_);
                    leanh::lean_del_object(v___x_2981_);
                    leanh::lean_dec(v_head_2979_);
                    leanh::lean_dec(v_tail_2976_);
                    leanh::lean_del_object(v___x_2973_);
                    leanh::lean_dec_ref(v_k_2904_);
                    return v___x_2990_;
                }
            }
            15 => {
                v_inheritedTraceOptions_2996_ = leanh::lean_ctor_get(v_a_2911_, 13);
                v_hasTrace_2997_ = leanh::lean_ctor_get_uint8(
                    v_options_2991_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v___x_2998_ = l_Lean_Expr_getAppFn_x27(v_a_2992_);
                v_nargs_2999_ = l_Lean_Expr_getAppNumArgs(v_a_2992_);
                v_dummy_3000_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__0,
                );
                leanh::lean_inc(v_nargs_2999_);
                v___x_3001_ = lean_mk_array(v_nargs_2999_, v_dummy_3000_);
                v___x_3002_ = leanh::lean_unsigned_to_nat(1);
                v___x_3003_ = lean_nat_sub(v_nargs_2999_, v___x_3002_);
                leanh::lean_dec(v_nargs_2999_);
                leanh::lean_inc(v_a_2992_);
                v___x_3004_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_a_2992_,
                    v___x_3001_,
                    v___x_3003_,
                );
                if v_hasTrace_2997_ == 0 {
                    v___y_3140_ = v_a_2905_;
                    v___y_3141_ = v_a_2906_;
                    v___y_3142_ = v_a_2907_;
                    v___y_3143_ = v_a_2908_;
                    v___y_3144_ = v_a_2909_;
                    v___y_3145_ = v_a_2910_;
                    v___y_3146_ = v_a_2911_;
                    v___y_3147_ = v_a_2912_;
                    state = 32;
                    continue;
                } else {
                    v___x_3155_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__15;
                    v___x_3156_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__18,
                    );
                    v___x_3157_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_2996_,
                        v_options_2991_,
                        v___x_3156_,
                    );
                    if v___x_3157_ == 0 {
                        v___y_3140_ = v_a_2905_;
                        v___y_3141_ = v_a_2906_;
                        v___y_3142_ = v_a_2907_;
                        v___y_3143_ = v_a_2908_;
                        v___y_3144_ = v_a_2909_;
                        v___y_3145_ = v_a_2910_;
                        v___y_3146_ = v_a_2911_;
                        v___y_3147_ = v_a_2912_;
                        state = 32;
                        continue;
                    } else {
                        v___x_3158_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20_once
                            ),
                            _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__20,
                        );
                        leanh::lean_inc_ref(v___x_2998_);
                        v___x_3159_ = l_Lean_MessageData_ofExpr(v___x_2998_);
                        v___x_3160_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3160_, 0, v___x_3158_);
                        leanh::lean_ctor_set(v___x_3160_, 1, v___x_3159_);
                        v___x_3161_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22_once
                            ),
                            _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__22,
                        );
                        v___x_3162_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3162_, 0, v___x_3160_);
                        leanh::lean_ctor_set(v___x_3162_, 1, v___x_3161_);
                        leanh::lean_inc_ref(v___x_3004_);
                        v___x_3163_ = lean_array_to_list(v___x_3004_);
                        v___x_3164_ = leanh::lean_box(0);
                        v___x_3165_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__2(v___x_3163_, v___x_3164_);
                        v___x_3166_ = l_Lean_MessageData_ofList(v___x_3165_);
                        v___x_3167_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3167_, 0, v___x_3162_);
                        leanh::lean_ctor_set(v___x_3167_, 1, v___x_3166_);
                        v___x_3168_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg(v___x_3155_, v___x_3167_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
                        if leanh::lean_obj_tag(v___x_3168_) == 0 {
                            leanh::lean_dec_ref_known(v___x_3168_, 1);
                            v___y_3140_ = v_a_2905_;
                            v___y_3141_ = v_a_2906_;
                            v___y_3142_ = v_a_2907_;
                            v___y_3143_ = v_a_2908_;
                            v___y_3144_ = v_a_2909_;
                            v___y_3145_ = v_a_2910_;
                            v___y_3146_ = v_a_2911_;
                            v___y_3147_ = v_a_2912_;
                            state = 32;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v___x_3004_);
                            leanh::lean_dec_ref(v___x_2998_);
                            leanh::lean_del_object(v___x_2994_);
                            leanh::lean_dec(v_a_2992_);
                            leanh::lean_del_object(v___x_2988_);
                            leanh::lean_dec_ref(v_hyps_2985_);
                            leanh::lean_dec_ref(v_00_u03c3s_2984_);
                            leanh::lean_dec(v_u_2983_);
                            leanh::lean_del_object(v___x_2981_);
                            leanh::lean_dec(v_head_2979_);
                            leanh::lean_dec(v_tail_2976_);
                            leanh::lean_del_object(v___x_2973_);
                            leanh::lean_dec_ref(v_k_2904_);
                            v_a_3169_ = leanh::lean_ctor_get(v___x_3168_, 0);
                            v_isSharedCheck_3176_ =
                                (!leanh::lean_is_exclusive(v___x_3168_)) as u8;
                            if v_isSharedCheck_3176_ == 0 {
                                v___x_3171_ = v___x_3168_;
                                v_isShared_3172_ = v_isSharedCheck_3176_;
                                state = 33;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3169_);
                                leanh::lean_dec(v___x_3168_);
                                v___x_3171_ = leanh::lean_box(0);
                                v_isShared_3172_ = v_isSharedCheck_3176_;
                                state = 33;
                                continue;
                            }
                        }
                    }
                }
            }
            16 => {
                if v___y_3017_ == 0 {
                    leanh::lean_dec_ref(v___x_3004_);
                    leanh::lean_del_object(v___x_2994_);
                    leanh::lean_del_object(v___x_2988_);
                    leanh::lean_dec_ref(v_hyps_2985_);
                    leanh::lean_dec_ref(v_00_u03c3s_2984_);
                    leanh::lean_dec(v_u_2983_);
                    leanh::lean_del_object(v___x_2981_);
                    leanh::lean_dec(v_head_2979_);
                    leanh::lean_dec(v_tail_2976_);
                    leanh::lean_del_object(v___x_2973_);
                    leanh::lean_dec_ref(v_k_2904_);
                    v___x_3018_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__2,
                    );
                    v___x_3019_ = l_Lean_MessageData_ofExpr(v_a_2992_);
                    v___x_3020_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3020_, 0, v___x_3018_);
                    leanh::lean_ctor_set(v___x_3020_, 1, v___x_3019_);
                    v___x_3021_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg(v___x_3020_, v___y_3016_, v___y_3014_, v___y_3008_, v___y_3006_);
                    return v___x_3021_;
                } else {
                    leanh::lean_dec(v_a_2992_);
                    v___x_3022_ = l_Lean_instInhabitedExpr;
                    v___x_3023_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3024_ = lean_array_get(v___x_3022_, v___x_3004_, v___x_3023_);
                    leanh::lean_inc(v___x_3024_);
                    if v_isShared_2995_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2994_, 1);
                        leanh::lean_ctor_set(v___x_2994_, 0, v___x_3024_);
                        v___x_3026_ = v___x_2994_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_3084_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3084_, 0, v___x_3024_);
                        v___x_3026_ = v_reuseFailAlloc_3084_;
                        state = 17;
                        continue;
                    }
                }
            }
            17 => {
                v___x_3027_ = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm(
                    v_head_2979_,
                    v___x_3026_,
                    v___y_3009_,
                    v___y_3010_,
                    v___y_3007_,
                    v___y_3012_,
                    v___y_3016_,
                    v___y_3014_,
                    v___y_3008_,
                    v___y_3006_,
                );
                if leanh::lean_obj_tag(v___x_3027_) == 0 {
                    v_a_3028_ = leanh::lean_ctor_get(v___x_3027_, 0);
                    leanh::lean_inc(v_a_3028_);
                    leanh::lean_dec_ref_known(v___x_3027_, 1);
                    if leanh::lean_obj_tag(v_a_3028_) == 1 {
                        v_val_3029_ = leanh::lean_ctor_get(v_a_3028_, 0);
                        leanh::lean_inc_n(v_val_3029_, 2);
                        leanh::lean_dec_ref_known(v_a_3028_, 1);
                        v___x_3030_ = leanh::lean_unsigned_to_nat(2);
                        v___x_3031_ = lean_array_get(v___x_3022_, v___x_3004_, v___x_3030_);
                        v___x_3032_ = lean_mk_empty_array_with_capacity(v___x_3002_);
                        v___x_3033_ = lean_array_push(v___x_3032_, v_val_3029_);
                        v___x_3034_ = leanh::lean_unsigned_to_nat(3);
                        v___x_3035_ = lean_array_get_size(v___x_3004_);
                        v___x_3036_ =
                            l_Array_toSubarray___redArg(v___x_3004_, v___x_3034_, v___x_3035_);
                        v___x_3037_ = l_Subarray_copy___redArg(v___x_3036_);
                        v___x_3038_ = l_Array_append___redArg(v___x_3033_, v___x_3037_);
                        leanh::lean_dec_ref(v___x_3037_);
                        leanh::lean_inc(v___x_3031_);
                        v___x_3039_ = l_Lean_Expr_beta(v___x_3031_, v___x_3038_);
                        leanh::lean_inc_ref(v_hyps_2985_);
                        leanh::lean_inc_ref(v_00_u03c3s_2984_);
                        leanh::lean_inc(v_u_2983_);
                        if v_isShared_2989_ == 0 {
                            leanh::lean_ctor_set(v___x_2988_, 3, v___x_3039_);
                            v___x_3041_ = v___x_2988_;
                            state = 18;
                            continue;
                        } else {
                            v_reuseFailAlloc_3073_ =
                                leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_u_2983_);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3073_,
                                1,
                                v_00_u03c3s_2984_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_3073_, 2, v_hyps_2985_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3073_, 3, v___x_3039_);
                            v___x_3041_ = v_reuseFailAlloc_3073_;
                            state = 18;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3028_);
                        leanh::lean_dec(v___x_3024_);
                        leanh::lean_dec_ref(v___x_3004_);
                        leanh::lean_del_object(v___x_2988_);
                        leanh::lean_dec_ref(v_hyps_2985_);
                        leanh::lean_dec_ref(v_00_u03c3s_2984_);
                        leanh::lean_dec(v_u_2983_);
                        leanh::lean_del_object(v___x_2981_);
                        leanh::lean_dec(v_tail_2976_);
                        leanh::lean_del_object(v___x_2973_);
                        leanh::lean_dec_ref(v_k_2904_);
                        v___x_3074_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5_once
                            ),
                            _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__5,
                        );
                        v___x_3075_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg(v___x_3074_, v___y_3016_, v___y_3014_, v___y_3008_, v___y_3006_);
                        return v___x_3075_;
                    }
                } else {
                    leanh::lean_dec(v___x_3024_);
                    leanh::lean_dec_ref(v___x_3004_);
                    leanh::lean_del_object(v___x_2988_);
                    leanh::lean_dec_ref(v_hyps_2985_);
                    leanh::lean_dec_ref(v_00_u03c3s_2984_);
                    leanh::lean_dec(v_u_2983_);
                    leanh::lean_del_object(v___x_2981_);
                    leanh::lean_dec(v_tail_2976_);
                    leanh::lean_del_object(v___x_2973_);
                    leanh::lean_dec_ref(v_k_2904_);
                    v_a_3076_ = leanh::lean_ctor_get(v___x_3027_, 0);
                    v_isSharedCheck_3083_ = (!leanh::lean_is_exclusive(v___x_3027_)) as u8;
                    if v_isSharedCheck_3083_ == 0 {
                        v___x_3078_ = v___x_3027_;
                        v_isShared_3079_ = v_isSharedCheck_3083_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3076_);
                        leanh::lean_dec(v___x_3027_);
                        v___x_3078_ = leanh::lean_box(0);
                        v_isShared_3079_ = v_isSharedCheck_3083_;
                        state = 25;
                        continue;
                    }
                }
            }
            18 => {
                if v_isShared_2974_ == 0 {
                    leanh::lean_ctor_set(v___x_2973_, 0, v_tail_2976_);
                    v___x_3043_ = v___x_2973_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3072_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_tail_2976_);
                    v___x_3043_ = v_reuseFailAlloc_3072_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_3044_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(
                    v___x_3041_,
                    v___x_3043_,
                    v_k_2904_,
                    v___y_3009_,
                    v___y_3010_,
                    v___y_3007_,
                    v___y_3012_,
                    v___y_3016_,
                    v___y_3014_,
                    v___y_3008_,
                    v___y_3006_,
                );
                if leanh::lean_obj_tag(v___x_3044_) == 0 {
                    v_a_3045_ = leanh::lean_ctor_get(v___x_3044_, 0);
                    leanh::lean_inc(v_a_3045_);
                    leanh::lean_dec_ref_known(v___x_3044_, 1);
                    leanh::lean_inc(v___x_3024_);
                    v___x_3046_ = l_Lean_Meta_getLevel(
                        v___x_3024_,
                        v___y_3016_,
                        v___y_3014_,
                        v___y_3008_,
                        v___y_3006_,
                    );
                    if leanh::lean_obj_tag(v___x_3046_) == 0 {
                        v_a_3047_ = leanh::lean_ctor_get(v___x_3046_, 0);
                        v_isSharedCheck_3063_ =
                            (!leanh::lean_is_exclusive(v___x_3046_)) as u8;
                        if v_isSharedCheck_3063_ == 0 {
                            v___x_3049_ = v___x_3046_;
                            v_isShared_3050_ = v_isSharedCheck_3063_;
                            state = 20;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3047_);
                            leanh::lean_dec(v___x_3046_);
                            v___x_3049_ = leanh::lean_box(0);
                            v_isShared_3050_ = v_isSharedCheck_3063_;
                            state = 20;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_3045_);
                        leanh::lean_dec(v___x_3031_);
                        leanh::lean_dec(v_val_3029_);
                        leanh::lean_dec(v___x_3024_);
                        leanh::lean_dec_ref(v_hyps_2985_);
                        leanh::lean_dec_ref(v_00_u03c3s_2984_);
                        leanh::lean_dec(v_u_2983_);
                        leanh::lean_del_object(v___x_2981_);
                        v_a_3064_ = leanh::lean_ctor_get(v___x_3046_, 0);
                        v_isSharedCheck_3071_ =
                            (!leanh::lean_is_exclusive(v___x_3046_)) as u8;
                        if v_isSharedCheck_3071_ == 0 {
                            v___x_3066_ = v___x_3046_;
                            v_isShared_3067_ = v_isSharedCheck_3071_;
                            state = 23;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3064_);
                            leanh::lean_dec(v___x_3046_);
                            v___x_3066_ = leanh::lean_box(0);
                            v_isShared_3067_ = v_isSharedCheck_3071_;
                            state = 23;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_3031_);
                    leanh::lean_dec(v_val_3029_);
                    leanh::lean_dec(v___x_3024_);
                    leanh::lean_dec_ref(v_hyps_2985_);
                    leanh::lean_dec_ref(v_00_u03c3s_2984_);
                    leanh::lean_dec(v_u_2983_);
                    leanh::lean_del_object(v___x_2981_);
                    return v___x_3044_;
                }
            }
            20 => {
                v___x_3051_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__3;
                leanh::lean_inc_ref(v___y_3011_);
                leanh::lean_inc_ref(v___y_3013_);
                leanh::lean_inc_ref(v___y_3015_);
                v___x_3052_ =
                    l_Lean_Name_mkStr4(v___y_3015_, v___y_3013_, v___y_3011_, v___x_3051_);
                v___x_3053_ = leanh::lean_box(0);
                if v_isShared_2982_ == 0 {
                    leanh::lean_ctor_set(v___x_2981_, 1, v___x_3053_);
                    leanh::lean_ctor_set(v___x_2981_, 0, v_u_2983_);
                    v___x_3055_ = v___x_2981_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3062_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_u_2983_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3062_, 1, v___x_3053_);
                    v___x_3055_ = v_reuseFailAlloc_3062_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_3056_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3056_, 0, v_a_3047_);
                leanh::lean_ctor_set(v___x_3056_, 1, v___x_3055_);
                v___x_3057_ = l_Lean_mkConst(v___x_3052_, v___x_3056_);
                v___x_3058_ = l_Lean_mkApp6(
                    v___x_3057_,
                    v___x_3024_,
                    v_00_u03c3s_2984_,
                    v_hyps_2985_,
                    v___x_3031_,
                    v_val_3029_,
                    v_a_3045_,
                );
                if v_isShared_3050_ == 0 {
                    leanh::lean_ctor_set(v___x_3049_, 0, v___x_3058_);
                    v___x_3060_ = v___x_3049_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3061_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3058_);
                    v___x_3060_ = v_reuseFailAlloc_3061_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3060_;
            }
            23 => {
                if v_isShared_3067_ == 0 {
                    v___x_3069_ = v___x_3066_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3070_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_a_3064_);
                    v___x_3069_ = v_reuseFailAlloc_3070_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3069_;
            }
            25 => {
                if v_isShared_3079_ == 0 {
                    v___x_3081_ = v___x_3078_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3082_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
                    v___x_3081_ = v_reuseFailAlloc_3082_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_3081_;
            }
            27 => {
                if v___y_3097_ == 0 {
                    v___x_3098_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__6;
                    leanh::lean_inc_ref(v___y_3092_);
                    leanh::lean_inc_ref(v___y_3094_);
                    leanh::lean_inc_ref(v___y_3096_);
                    v___x_3099_ =
                        l_Lean_Name_mkStr4(v___y_3096_, v___y_3094_, v___y_3092_, v___x_3098_);
                    v___x_3100_ = l_Lean_Expr_isConstOf(v___x_2998_, v___x_3099_);
                    leanh::lean_dec(v___x_3099_);
                    leanh::lean_dec_ref(v___x_2998_);
                    if v___x_3100_ == 0 {
                        v___y_3006_ = v___y_3086_;
                        v___y_3007_ = v___y_3087_;
                        v___y_3008_ = v___y_3088_;
                        v___y_3009_ = v___y_3089_;
                        v___y_3010_ = v___y_3090_;
                        v___y_3011_ = v___y_3092_;
                        v___y_3012_ = v___y_3091_;
                        v___y_3013_ = v___y_3094_;
                        v___y_3014_ = v___y_3093_;
                        v___y_3015_ = v___y_3096_;
                        v___y_3016_ = v___y_3095_;
                        v___y_3017_ = v___x_3100_;
                        state = 16;
                        continue;
                    } else {
                        v___x_3101_ = leanh::lean_box(0);
                        v___x_3102_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___lam__0(
                            v___x_3004_,
                            v___x_3101_,
                        );
                        v___y_3006_ = v___y_3086_;
                        v___y_3007_ = v___y_3087_;
                        v___y_3008_ = v___y_3088_;
                        v___y_3009_ = v___y_3089_;
                        v___y_3010_ = v___y_3090_;
                        v___y_3011_ = v___y_3092_;
                        v___y_3012_ = v___y_3091_;
                        v___y_3013_ = v___y_3094_;
                        v___y_3014_ = v___y_3093_;
                        v___y_3015_ = v___y_3096_;
                        v___y_3016_ = v___y_3095_;
                        v___y_3017_ = v___x_3102_;
                        state = 16;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_2998_);
                    leanh::lean_del_object(v___x_2994_);
                    leanh::lean_dec(v_a_2992_);
                    leanh::lean_del_object(v___x_2988_);
                    leanh::lean_del_object(v___x_2981_);
                    leanh::lean_del_object(v___x_2973_);
                    v___x_3103_ = l_Lean_instInhabitedExpr;
                    v___x_3104_ = lean_array_get(v___x_3103_, v___x_3004_, v___x_3002_);
                    v___x_3105_ = leanh::lean_unsigned_to_nat(3);
                    v___x_3106_ = lean_array_get_size(v___x_3004_);
                    leanh::lean_inc_ref(v___x_3004_);
                    v___x_3107_ =
                        l_Array_toSubarray___redArg(v___x_3004_, v___x_3105_, v___x_3106_);
                    v___x_3108_ = l_Subarray_copy___redArg(v___x_3107_);
                    leanh::lean_inc_ref(v___x_3108_);
                    v___x_3109_ = l_Lean_Expr_beta(v___x_3104_, v___x_3108_);
                    leanh::lean_inc_ref(v___x_3109_);
                    leanh::lean_inc_ref(v_hyps_2985_);
                    leanh::lean_inc_ref(v_00_u03c3s_2984_);
                    leanh::lean_inc(v_u_2983_);
                    v___x_3110_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_3110_, 0, v_u_2983_);
                    leanh::lean_ctor_set(v___x_3110_, 1, v_00_u03c3s_2984_);
                    leanh::lean_ctor_set(v___x_3110_, 2, v_hyps_2985_);
                    leanh::lean_ctor_set(v___x_3110_, 3, v___x_3109_);
                    leanh::lean_inc_ref(v_k_2904_);
                    v___x_3111_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(
                        v___x_3110_,
                        v_head_2979_,
                        v_k_2904_,
                        v___y_3089_,
                        v___y_3090_,
                        v___y_3087_,
                        v___y_3091_,
                        v___y_3095_,
                        v___y_3093_,
                        v___y_3088_,
                        v___y_3086_,
                    );
                    if leanh::lean_obj_tag(v___x_3111_) == 0 {
                        v_a_3112_ = leanh::lean_ctor_get(v___x_3111_, 0);
                        v_isSharedCheck_3138_ =
                            (!leanh::lean_is_exclusive(v___x_3111_)) as u8;
                        if v_isSharedCheck_3138_ == 0 {
                            v___x_3114_ = v___x_3111_;
                            v_isShared_3115_ = v_isSharedCheck_3138_;
                            state = 28;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3112_);
                            leanh::lean_dec(v___x_3111_);
                            v___x_3114_ = leanh::lean_box(0);
                            v_isShared_3115_ = v_isSharedCheck_3138_;
                            state = 28;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_3109_);
                        leanh::lean_dec_ref(v___x_3108_);
                        leanh::lean_dec_ref(v___x_3004_);
                        leanh::lean_dec_ref(v_hyps_2985_);
                        leanh::lean_dec_ref(v_00_u03c3s_2984_);
                        leanh::lean_dec(v_u_2983_);
                        leanh::lean_dec(v_tail_2976_);
                        leanh::lean_dec_ref(v_k_2904_);
                        return v___x_3111_;
                    }
                }
            }
            28 => {
                v___x_3116_ = leanh::lean_unsigned_to_nat(2);
                v___x_3117_ = lean_array_get(v___x_3103_, v___x_3004_, v___x_3116_);
                leanh::lean_dec_ref(v___x_3004_);
                v___x_3118_ = l_Lean_Expr_beta(v___x_3117_, v___x_3108_);
                leanh::lean_inc_ref(v___x_3118_);
                leanh::lean_inc_ref(v_hyps_2985_);
                leanh::lean_inc_ref(v_00_u03c3s_2984_);
                leanh::lean_inc(v_u_2983_);
                v___x_3119_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3119_, 0, v_u_2983_);
                leanh::lean_ctor_set(v___x_3119_, 1, v_00_u03c3s_2984_);
                leanh::lean_ctor_set(v___x_3119_, 2, v_hyps_2985_);
                leanh::lean_ctor_set(v___x_3119_, 3, v___x_3118_);
                if v_isShared_3115_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3114_, 1);
                    leanh::lean_ctor_set(v___x_3114_, 0, v_tail_2976_);
                    v___x_3121_ = v___x_3114_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3137_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_tail_2976_);
                    v___x_3121_ = v_reuseFailAlloc_3137_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                v___x_3122_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(
                    v___x_3119_,
                    v___x_3121_,
                    v_k_2904_,
                    v___y_3089_,
                    v___y_3090_,
                    v___y_3087_,
                    v___y_3091_,
                    v___y_3095_,
                    v___y_3093_,
                    v___y_3088_,
                    v___y_3086_,
                );
                if leanh::lean_obj_tag(v___x_3122_) == 0 {
                    v_a_3123_ = leanh::lean_ctor_get(v___x_3122_, 0);
                    v_isSharedCheck_3136_ = (!leanh::lean_is_exclusive(v___x_3122_)) as u8;
                    if v_isSharedCheck_3136_ == 0 {
                        v___x_3125_ = v___x_3122_;
                        v_isShared_3126_ = v_isSharedCheck_3136_;
                        state = 30;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3123_);
                        leanh::lean_dec(v___x_3122_);
                        v___x_3125_ = leanh::lean_box(0);
                        v_isShared_3126_ = v_isSharedCheck_3136_;
                        state = 30;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_3118_);
                    leanh::lean_dec(v_a_3112_);
                    leanh::lean_dec_ref(v___x_3109_);
                    leanh::lean_dec_ref(v_hyps_2985_);
                    leanh::lean_dec_ref(v_00_u03c3s_2984_);
                    leanh::lean_dec(v_u_2983_);
                    return v___x_3122_;
                }
            }
            30 => {
                v___x_3127_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__7;
                leanh::lean_inc_ref(v___y_3092_);
                leanh::lean_inc_ref(v___y_3094_);
                leanh::lean_inc_ref(v___y_3096_);
                v___x_3128_ =
                    l_Lean_Name_mkStr4(v___y_3096_, v___y_3094_, v___y_3092_, v___x_3127_);
                v___x_3129_ = leanh::lean_box(0);
                v___x_3130_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3130_, 0, v_u_2983_);
                leanh::lean_ctor_set(v___x_3130_, 1, v___x_3129_);
                v___x_3131_ = l_Lean_mkConst(v___x_3128_, v___x_3130_);
                v___x_3132_ = l_Lean_mkApp6(
                    v___x_3131_,
                    v_00_u03c3s_2984_,
                    v_hyps_2985_,
                    v___x_3109_,
                    v___x_3118_,
                    v_a_3112_,
                    v_a_3123_,
                );
                if v_isShared_3126_ == 0 {
                    leanh::lean_ctor_set(v___x_3125_, 0, v___x_3132_);
                    v___x_3134_ = v___x_3125_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_3135_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3135_, 0, v___x_3132_);
                    v___x_3134_ = v_reuseFailAlloc_3135_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_3134_;
            }
            32 => {
                v___x_3148_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__8;
                v___x_3149_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__9;
                v___x_3150_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__10;
                v___x_3151_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__12;
                v___x_3152_ = l_Lean_Expr_isConstOf(v___x_2998_, v___x_3151_);
                if v___x_3152_ == 0 {
                    v___y_3086_ = v___y_3147_;
                    v___y_3087_ = v___y_3142_;
                    v___y_3088_ = v___y_3146_;
                    v___y_3089_ = v___y_3140_;
                    v___y_3090_ = v___y_3141_;
                    v___y_3091_ = v___y_3143_;
                    v___y_3092_ = v___x_3150_;
                    v___y_3093_ = v___y_3145_;
                    v___y_3094_ = v___x_3149_;
                    v___y_3095_ = v___y_3144_;
                    v___y_3096_ = v___x_3148_;
                    v___y_3097_ = v___x_3152_;
                    state = 27;
                    continue;
                } else {
                    v___x_3153_ = leanh::lean_box(0);
                    v___x_3154_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___lam__0(
                        v___x_3004_,
                        v___x_3153_,
                    );
                    v___y_3086_ = v___y_3147_;
                    v___y_3087_ = v___y_3142_;
                    v___y_3088_ = v___y_3146_;
                    v___y_3089_ = v___y_3140_;
                    v___y_3090_ = v___y_3141_;
                    v___y_3091_ = v___y_3143_;
                    v___y_3092_ = v___x_3150_;
                    v___y_3093_ = v___y_3145_;
                    v___y_3094_ = v___x_3149_;
                    v___y_3095_ = v___y_3144_;
                    v___y_3096_ = v___x_3148_;
                    v___y_3097_ = v___x_3154_;
                    state = 27;
                    continue;
                }
            }
            33 => {
                if v_isShared_3172_ == 0 {
                    v___x_3174_ = v___x_3171_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_3175_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3169_);
                    v___x_3174_ = v_reuseFailAlloc_3175_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_3174_;
            }
            35 => {
                if leanh::lean_obj_tag(v_a_3188_) == 1 {
                    leanh::lean_dec_ref(v_goal_2902_);
                    v_val_3192_ = leanh::lean_ctor_get(v_a_3188_, 0);
                    leanh::lean_inc(v_val_3192_);
                    leanh::lean_dec_ref_known(v_a_3188_, 1);
                    if v_isShared_3191_ == 0 {
                        leanh::lean_ctor_set(v___x_3190_, 0, v_val_3192_);
                        v___x_3194_ = v___x_3190_;
                        state = 36;
                        continue;
                    } else {
                        v_reuseFailAlloc_3195_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_val_3192_);
                        v___x_3194_ = v_reuseFailAlloc_3195_;
                        state = 36;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3190_);
                    leanh::lean_dec(v_a_3188_);
                    v_target_3196_ = leanh::lean_ctor_get(v_goal_2902_, 3);
                    leanh::lean_inc_ref(v_target_3196_);
                    leanh::lean_dec_ref(v_goal_2902_);
                    v___x_3197_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24,
                    );
                    v___x_3198_ = l_Lean_MessageData_ofExpr(v_target_3196_);
                    v___x_3199_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3199_, 0, v___x_3197_);
                    leanh::lean_ctor_set(v___x_3199_, 1, v___x_3198_);
                    v___x_3200_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26,
                    );
                    v___x_3201_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3201_, 0, v___x_3199_);
                    leanh::lean_ctor_set(v___x_3201_, 1, v___x_3200_);
                    v___x_3202_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg(v___x_3201_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
                    return v___x_3202_;
                }
            }
            36 => {
                return v___x_3194_;
            }
            37 => {
                if v_isShared_3207_ == 0 {
                    v___x_3209_ = v___x_3206_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3210_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_a_3204_);
                    v___x_3209_ = v_reuseFailAlloc_3210_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3209_;
            }
            39 => {
                if leanh::lean_obj_tag(v_a_3217_) == 1 {
                    leanh::lean_dec_ref(v_goal_2902_);
                    v_val_3221_ = leanh::lean_ctor_get(v_a_3217_, 0);
                    leanh::lean_inc(v_val_3221_);
                    leanh::lean_dec_ref_known(v_a_3217_, 1);
                    if v_isShared_3220_ == 0 {
                        leanh::lean_ctor_set(v___x_3219_, 0, v_val_3221_);
                        v___x_3223_ = v___x_3219_;
                        state = 40;
                        continue;
                    } else {
                        v_reuseFailAlloc_3224_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_val_3221_);
                        v___x_3223_ = v_reuseFailAlloc_3224_;
                        state = 40;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3219_);
                    leanh::lean_dec(v_a_3217_);
                    v_target_3225_ = leanh::lean_ctor_get(v_goal_2902_, 3);
                    leanh::lean_inc_ref(v_target_3225_);
                    leanh::lean_dec_ref(v_goal_2902_);
                    v___x_3226_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__24,
                    );
                    v___x_3227_ = l_Lean_MessageData_ofExpr(v_target_3225_);
                    v___x_3228_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3228_, 0, v___x_3226_);
                    leanh::lean_ctor_set(v___x_3228_, 1, v___x_3227_);
                    v___x_3229_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__26,
                    );
                    v___x_3230_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3230_, 0, v___x_3228_);
                    leanh::lean_ctor_set(v___x_3230_, 1, v___x_3229_);
                    v___x_3231_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg(v___x_3230_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
                    return v___x_3231_;
                }
            }
            40 => {
                return v___x_3223_;
            }
            41 => {
                if v_isShared_3236_ == 0 {
                    v___x_3238_ = v___x_3235_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_3239_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_a_3233_);
                    v___x_3238_ = v_reuseFailAlloc_3239_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_3238_;
            }
            43 => {
                if leanh::lean_obj_tag(v_a_3242_) == 1 {
                    leanh::lean_dec(v_name_3213_);
                    v_val_3246_ = leanh::lean_ctor_get(v_a_3242_, 0);
                    leanh::lean_inc(v_val_3246_);
                    leanh::lean_dec_ref_known(v_a_3242_, 1);
                    if v_isShared_3245_ == 0 {
                        leanh::lean_ctor_set(v___x_3244_, 0, v_val_3246_);
                        v___x_3248_ = v___x_3244_;
                        state = 44;
                        continue;
                    } else {
                        v_reuseFailAlloc_3249_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_val_3246_);
                        v___x_3248_ = v_reuseFailAlloc_3249_;
                        state = 44;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3244_);
                    leanh::lean_dec(v_a_3242_);
                    v___x_3250_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__28
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__28_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__28,
                    );
                    v___x_3251_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_name_3213_);
                    v___x_3252_ = l_Lean_MessageData_ofFormat(v___x_3251_);
                    v___x_3253_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3253_, 0, v___x_3250_);
                    leanh::lean_ctor_set(v___x_3253_, 1, v___x_3252_);
                    v___x_3254_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__30
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__30_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__30,
                    );
                    v___x_3255_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3255_, 0, v___x_3253_);
                    leanh::lean_ctor_set(v___x_3255_, 1, v___x_3254_);
                    v___x_3256_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg(v___x_3255_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
                    return v___x_3256_;
                }
            }
            44 => {
                return v___x_3248_;
            }
            45 => {
                if v_isShared_3261_ == 0 {
                    v___x_3263_ = v___x_3260_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_3264_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3258_);
                    v___x_3263_ = v_reuseFailAlloc_3264_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_3263_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1(
    mut v_00_u03b1_3268_: *mut leanh::LeanObject,
    mut v_msg_3269_: *mut leanh::LeanObject,
    mut v___y_3270_: *mut leanh::LeanObject,
    mut v___y_3271_: *mut leanh::LeanObject,
    mut v___y_3272_: *mut leanh::LeanObject,
    mut v___y_3273_: *mut leanh::LeanObject,
    mut v___y_3274_: *mut leanh::LeanObject,
    mut v___y_3275_: *mut leanh::LeanObject,
    mut v___y_3276_: *mut leanh::LeanObject,
    mut v___y_3277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3279_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg(
            v_msg_3269_,
            v___y_3274_,
            v___y_3275_,
            v___y_3276_,
            v___y_3277_,
        );
    return v___x_3279_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___boxed(
    mut v_00_u03b1_3280_: *mut leanh::LeanObject,
    mut v_msg_3281_: *mut leanh::LeanObject,
    mut v___y_3282_: *mut leanh::LeanObject,
    mut v___y_3283_: *mut leanh::LeanObject,
    mut v___y_3284_: *mut leanh::LeanObject,
    mut v___y_3285_: *mut leanh::LeanObject,
    mut v___y_3286_: *mut leanh::LeanObject,
    mut v___y_3287_: *mut leanh::LeanObject,
    mut v___y_3288_: *mut leanh::LeanObject,
    mut v___y_3289_: *mut leanh::LeanObject,
    mut v___y_3290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3291_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1(
        v_00_u03b1_3280_,
        v_msg_3281_,
        v___y_3282_,
        v___y_3283_,
        v___y_3284_,
        v___y_3285_,
        v___y_3286_,
        v___y_3287_,
        v___y_3288_,
        v___y_3289_,
    );
    leanh::lean_dec(v___y_3289_);
    leanh::lean_dec_ref(v___y_3288_);
    leanh::lean_dec(v___y_3287_);
    leanh::lean_dec_ref(v___y_3286_);
    leanh::lean_dec(v___y_3285_);
    leanh::lean_dec_ref(v___y_3284_);
    leanh::lean_dec(v___y_3283_);
    leanh::lean_dec_ref(v___y_3282_);
    return v_res_3291_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3(
    mut v_cls_3292_: *mut leanh::LeanObject,
    mut v_msg_3293_: *mut leanh::LeanObject,
    mut v___y_3294_: *mut leanh::LeanObject,
    mut v___y_3295_: *mut leanh::LeanObject,
    mut v___y_3296_: *mut leanh::LeanObject,
    mut v___y_3297_: *mut leanh::LeanObject,
    mut v___y_3298_: *mut leanh::LeanObject,
    mut v___y_3299_: *mut leanh::LeanObject,
    mut v___y_3300_: *mut leanh::LeanObject,
    mut v___y_3301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3303_ =
        l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg(
            v_cls_3292_,
            v_msg_3293_,
            v___y_3298_,
            v___y_3299_,
            v___y_3300_,
            v___y_3301_,
        );
    return v___x_3303_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___boxed(
    mut v_cls_3304_: *mut leanh::LeanObject,
    mut v_msg_3305_: *mut leanh::LeanObject,
    mut v___y_3306_: *mut leanh::LeanObject,
    mut v___y_3307_: *mut leanh::LeanObject,
    mut v___y_3308_: *mut leanh::LeanObject,
    mut v___y_3309_: *mut leanh::LeanObject,
    mut v___y_3310_: *mut leanh::LeanObject,
    mut v___y_3311_: *mut leanh::LeanObject,
    mut v___y_3312_: *mut leanh::LeanObject,
    mut v___y_3313_: *mut leanh::LeanObject,
    mut v___y_3314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3315_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3(
        v_cls_3304_,
        v_msg_3305_,
        v___y_3306_,
        v___y_3307_,
        v___y_3308_,
        v___y_3309_,
        v___y_3310_,
        v___y_3311_,
        v___y_3312_,
        v___y_3313_,
    );
    leanh::lean_dec(v___y_3313_);
    leanh::lean_dec_ref(v___y_3312_);
    leanh::lean_dec(v___y_3311_);
    leanh::lean_dec_ref(v___y_3310_);
    leanh::lean_dec(v___y_3309_);
    leanh::lean_dec_ref(v___y_3308_);
    leanh::lean_dec(v___y_3307_);
    leanh::lean_dec_ref(v___y_3306_);
    return v_res_3315_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4(
    mut v_00_u03b1_3316_: *mut leanh::LeanObject,
    mut v_msg_3317_: *mut leanh::LeanObject,
    mut v___y_3318_: *mut leanh::LeanObject,
    mut v___y_3319_: *mut leanh::LeanObject,
    mut v___y_3320_: *mut leanh::LeanObject,
    mut v___y_3321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3323_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___redArg(
            v_msg_3317_,
            v___y_3318_,
            v___y_3319_,
            v___y_3320_,
            v___y_3321_,
        );
    return v___x_3323_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4___boxed(
    mut v_00_u03b1_3324_: *mut leanh::LeanObject,
    mut v_msg_3325_: *mut leanh::LeanObject,
    mut v___y_3326_: *mut leanh::LeanObject,
    mut v___y_3327_: *mut leanh::LeanObject,
    mut v___y_3328_: *mut leanh::LeanObject,
    mut v___y_3329_: *mut leanh::LeanObject,
    mut v___y_3330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3331_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__4(
        v_00_u03b1_3324_,
        v_msg_3325_,
        v___y_3326_,
        v___y_3327_,
        v___y_3328_,
        v___y_3329_,
    );
    leanh::lean_dec(v___y_3329_);
    leanh::lean_dec_ref(v___y_3328_);
    leanh::lean_dec(v___y_3327_);
    leanh::lean_dec_ref(v___y_3326_);
    return v_res_3331_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg___lam__0(
    mut v_x_3332_: *mut leanh::LeanObject,
    mut v___y_3333_: *mut leanh::LeanObject,
    mut v___y_3334_: *mut leanh::LeanObject,
    mut v___y_3335_: *mut leanh::LeanObject,
    mut v___y_3336_: *mut leanh::LeanObject,
    mut v___y_3337_: *mut leanh::LeanObject,
    mut v___y_3338_: *mut leanh::LeanObject,
    mut v___y_3339_: *mut leanh::LeanObject,
    mut v___y_3340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_3336_);
    leanh::lean_inc_ref(v___y_3335_);
    leanh::lean_inc(v___y_3334_);
    leanh::lean_inc_ref(v___y_3333_);
    v___x_3342_ = leanh::lean_apply_9(
        v_x_3332_,
        v___y_3333_,
        v___y_3334_,
        v___y_3335_,
        v___y_3336_,
        v___y_3337_,
        v___y_3338_,
        v___y_3339_,
        v___y_3340_,
        leanh::lean_box(0),
    );
    return v___x_3342_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg___lam__0___boxed(
    mut v_x_3343_: *mut leanh::LeanObject,
    mut v___y_3344_: *mut leanh::LeanObject,
    mut v___y_3345_: *mut leanh::LeanObject,
    mut v___y_3346_: *mut leanh::LeanObject,
    mut v___y_3347_: *mut leanh::LeanObject,
    mut v___y_3348_: *mut leanh::LeanObject,
    mut v___y_3349_: *mut leanh::LeanObject,
    mut v___y_3350_: *mut leanh::LeanObject,
    mut v___y_3351_: *mut leanh::LeanObject,
    mut v___y_3352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3353_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg___lam__0(v_x_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
    leanh::lean_dec(v___y_3347_);
    leanh::lean_dec_ref(v___y_3346_);
    leanh::lean_dec(v___y_3345_);
    leanh::lean_dec_ref(v___y_3344_);
    return v_res_3353_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg(
    mut v_mvarId_3354_: *mut leanh::LeanObject,
    mut v_x_3355_: *mut leanh::LeanObject,
    mut v___y_3356_: *mut leanh::LeanObject,
    mut v___y_3357_: *mut leanh::LeanObject,
    mut v___y_3358_: *mut leanh::LeanObject,
    mut v___y_3359_: *mut leanh::LeanObject,
    mut v___y_3360_: *mut leanh::LeanObject,
    mut v___y_3361_: *mut leanh::LeanObject,
    mut v___y_3362_: *mut leanh::LeanObject,
    mut v___y_3363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3370_: u8 = 0;
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3374_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_3359_);
                leanh::lean_inc_ref(v___y_3358_);
                leanh::lean_inc(v___y_3357_);
                leanh::lean_inc_ref(v___y_3356_);
                v___f_3365_ = leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                leanh::lean_closure_set(v___f_3365_, 0, v_x_3355_);
                leanh::lean_closure_set(v___f_3365_, 1, v___y_3356_);
                leanh::lean_closure_set(v___f_3365_, 2, v___y_3357_);
                leanh::lean_closure_set(v___f_3365_, 3, v___y_3358_);
                leanh::lean_closure_set(v___f_3365_, 4, v___y_3359_);
                v___x_3366_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_3354_,
                    v___f_3365_,
                    v___y_3360_,
                    v___y_3361_,
                    v___y_3362_,
                    v___y_3363_,
                );
                if leanh::lean_obj_tag(v___x_3366_) == 0 {
                    return v___x_3366_;
                } else {
                    v_a_3367_ = leanh::lean_ctor_get(v___x_3366_, 0);
                    v_isSharedCheck_3374_ = (!leanh::lean_is_exclusive(v___x_3366_)) as u8;
                    if v_isSharedCheck_3374_ == 0 {
                        v___x_3369_ = v___x_3366_;
                        v_isShared_3370_ = v_isSharedCheck_3374_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3367_);
                        leanh::lean_dec(v___x_3366_);
                        v___x_3369_ = leanh::lean_box(0);
                        v_isShared_3370_ = v_isSharedCheck_3374_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3370_ == 0 {
                    v___x_3372_ = v___x_3369_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3373_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_a_3367_);
                    v___x_3372_ = v_reuseFailAlloc_3373_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3372_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg___boxed(
    mut v_mvarId_3375_: *mut leanh::LeanObject,
    mut v_x_3376_: *mut leanh::LeanObject,
    mut v___y_3377_: *mut leanh::LeanObject,
    mut v___y_3378_: *mut leanh::LeanObject,
    mut v___y_3379_: *mut leanh::LeanObject,
    mut v___y_3380_: *mut leanh::LeanObject,
    mut v___y_3381_: *mut leanh::LeanObject,
    mut v___y_3382_: *mut leanh::LeanObject,
    mut v___y_3383_: *mut leanh::LeanObject,
    mut v___y_3384_: *mut leanh::LeanObject,
    mut v___y_3385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3386_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg(v_mvarId_3375_, v_x_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
    leanh::lean_dec(v___y_3384_);
    leanh::lean_dec_ref(v___y_3383_);
    leanh::lean_dec(v___y_3382_);
    leanh::lean_dec_ref(v___y_3381_);
    leanh::lean_dec(v___y_3380_);
    leanh::lean_dec_ref(v___y_3379_);
    leanh::lean_dec(v___y_3378_);
    leanh::lean_dec_ref(v___y_3377_);
    return v_res_3386_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2(
    mut v_00_u03b1_3387_: *mut leanh::LeanObject,
    mut v_mvarId_3388_: *mut leanh::LeanObject,
    mut v_x_3389_: *mut leanh::LeanObject,
    mut v___y_3390_: *mut leanh::LeanObject,
    mut v___y_3391_: *mut leanh::LeanObject,
    mut v___y_3392_: *mut leanh::LeanObject,
    mut v___y_3393_: *mut leanh::LeanObject,
    mut v___y_3394_: *mut leanh::LeanObject,
    mut v___y_3395_: *mut leanh::LeanObject,
    mut v___y_3396_: *mut leanh::LeanObject,
    mut v___y_3397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3399_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg(v_mvarId_3388_, v_x_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
    return v___x_3399_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___boxed(
    mut v_00_u03b1_3400_: *mut leanh::LeanObject,
    mut v_mvarId_3401_: *mut leanh::LeanObject,
    mut v_x_3402_: *mut leanh::LeanObject,
    mut v___y_3403_: *mut leanh::LeanObject,
    mut v___y_3404_: *mut leanh::LeanObject,
    mut v___y_3405_: *mut leanh::LeanObject,
    mut v___y_3406_: *mut leanh::LeanObject,
    mut v___y_3407_: *mut leanh::LeanObject,
    mut v___y_3408_: *mut leanh::LeanObject,
    mut v___y_3409_: *mut leanh::LeanObject,
    mut v___y_3410_: *mut leanh::LeanObject,
    mut v___y_3411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3412_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2(
            v_00_u03b1_3400_,
            v_mvarId_3401_,
            v_x_3402_,
            v___y_3403_,
            v___y_3404_,
            v___y_3405_,
            v___y_3406_,
            v___y_3407_,
            v___y_3408_,
            v___y_3409_,
            v___y_3410_,
        );
    leanh::lean_dec(v___y_3410_);
    leanh::lean_dec_ref(v___y_3409_);
    leanh::lean_dec(v___y_3408_);
    leanh::lean_dec_ref(v___y_3407_);
    leanh::lean_dec(v___y_3406_);
    leanh::lean_dec_ref(v___y_3405_);
    leanh::lean_dec(v___y_3404_);
    leanh::lean_dec_ref(v___y_3403_);
    return v_res_3412_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__0(
    mut v_val_3413_: *mut leanh::LeanObject,
    mut v_goal_3414_: *mut leanh::LeanObject,
    mut v_name_3415_: *mut leanh::LeanObject,
    mut v___y_3416_: *mut leanh::LeanObject,
    mut v___y_3417_: *mut leanh::LeanObject,
    mut v___y_3418_: *mut leanh::LeanObject,
    mut v___y_3419_: *mut leanh::LeanObject,
    mut v___y_3420_: *mut leanh::LeanObject,
    mut v___y_3421_: *mut leanh::LeanObject,
    mut v___y_3422_: *mut leanh::LeanObject,
    mut v___y_3423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3431_: u8 = 0;
    let mut v___x_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3439_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3425_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_goal_3414_);
                v___x_3426_ = l_Lean_Syntax_getId(v_name_3415_);
                v___x_3427_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                    v___x_3425_,
                    v___x_3426_,
                    v___y_3420_,
                    v___y_3421_,
                    v___y_3422_,
                    v___y_3423_,
                );
                if leanh::lean_obj_tag(v___x_3427_) == 0 {
                    v_a_3428_ = leanh::lean_ctor_get(v___x_3427_, 0);
                    v_isSharedCheck_3439_ = (!leanh::lean_is_exclusive(v___x_3427_)) as u8;
                    if v_isSharedCheck_3439_ == 0 {
                        v___x_3430_ = v___x_3427_;
                        v_isShared_3431_ = v_isSharedCheck_3439_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3428_);
                        leanh::lean_dec(v___x_3427_);
                        v___x_3430_ = leanh::lean_box(0);
                        v_isShared_3431_ = v_isSharedCheck_3439_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_3427_;
                }
            }
            1 => {
                v___x_3432_ = lean_st_ref_take(v_val_3413_);
                v___x_3433_ = l_Lean_Expr_mvarId_x21(v_a_3428_);
                v___x_3434_ = lean_array_push(v___x_3432_, v___x_3433_);
                v___x_3435_ = lean_st_ref_set(v_val_3413_, v___x_3434_);
                if v_isShared_3431_ == 0 {
                    v___x_3437_ = v___x_3430_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3438_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_a_3428_);
                    v___x_3437_ = v_reuseFailAlloc_3438_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3437_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__0___boxed(
    mut v_val_3440_: *mut leanh::LeanObject,
    mut v_goal_3441_: *mut leanh::LeanObject,
    mut v_name_3442_: *mut leanh::LeanObject,
    mut v___y_3443_: *mut leanh::LeanObject,
    mut v___y_3444_: *mut leanh::LeanObject,
    mut v___y_3445_: *mut leanh::LeanObject,
    mut v___y_3446_: *mut leanh::LeanObject,
    mut v___y_3447_: *mut leanh::LeanObject,
    mut v___y_3448_: *mut leanh::LeanObject,
    mut v___y_3449_: *mut leanh::LeanObject,
    mut v___y_3450_: *mut leanh::LeanObject,
    mut v___y_3451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3452_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__0(
        v_val_3440_,
        v_goal_3441_,
        v_name_3442_,
        v___y_3443_,
        v___y_3444_,
        v___y_3445_,
        v___y_3446_,
        v___y_3447_,
        v___y_3448_,
        v___y_3449_,
        v___y_3450_,
    );
    leanh::lean_dec(v___y_3450_);
    leanh::lean_dec_ref(v___y_3449_);
    leanh::lean_dec(v___y_3448_);
    leanh::lean_dec_ref(v___y_3447_);
    leanh::lean_dec(v___y_3446_);
    leanh::lean_dec_ref(v___y_3445_);
    leanh::lean_dec(v___y_3444_);
    leanh::lean_dec_ref(v___y_3443_);
    leanh::lean_dec(v_name_3442_);
    leanh::lean_dec(v_val_3440_);
    return v_res_3452_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15_spec__17___redArg(
    mut v_x_3453_: *mut leanh::LeanObject,
    mut v_x_3454_: *mut leanh::LeanObject,
    mut v_x_3455_: *mut leanh::LeanObject,
    mut v_x_3456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3461_: u8 = 0;
    let mut v___x_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: u8 = 0;
    let mut v___x_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: u8 = 0;
    let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3482_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3457_ = leanh::lean_ctor_get(v_x_3453_, 0);
                v_vs_3458_ = leanh::lean_ctor_get(v_x_3453_, 1);
                v_isSharedCheck_3482_ = (!leanh::lean_is_exclusive(v_x_3453_)) as u8;
                if v_isSharedCheck_3482_ == 0 {
                    v___x_3460_ = v_x_3453_;
                    v_isShared_3461_ = v_isSharedCheck_3482_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_3458_);
                    leanh::lean_inc(v_ks_3457_);
                    leanh::lean_dec(v_x_3453_);
                    v___x_3460_ = leanh::lean_box(0);
                    v_isShared_3461_ = v_isSharedCheck_3482_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3462_ = lean_array_get_size(v_ks_3457_);
                v___x_3463_ = lean_nat_dec_lt(v_x_3454_, v___x_3462_);
                if v___x_3463_ == 0 {
                    leanh::lean_dec(v_x_3454_);
                    v___x_3464_ = lean_array_push(v_ks_3457_, v_x_3455_);
                    v___x_3465_ = lean_array_push(v_vs_3458_, v_x_3456_);
                    if v_isShared_3461_ == 0 {
                        leanh::lean_ctor_set(v___x_3460_, 1, v___x_3465_);
                        leanh::lean_ctor_set(v___x_3460_, 0, v___x_3464_);
                        v___x_3467_ = v___x_3460_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3468_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3464_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3468_, 1, v___x_3465_);
                        v___x_3467_ = v_reuseFailAlloc_3468_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3469_ = lean_array_fget_borrowed(v_ks_3457_, v_x_3454_);
                    v___x_3470_ = l_Lean_instBEqMVarId_beq(v_x_3455_, v_k_x27_3469_);
                    if v___x_3470_ == 0 {
                        if v_isShared_3461_ == 0 {
                            v___x_3472_ = v___x_3460_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3476_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_ks_3457_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3476_, 1, v_vs_3458_);
                            v___x_3472_ = v_reuseFailAlloc_3476_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3477_ = lean_array_fset(v_ks_3457_, v_x_3454_, v_x_3455_);
                        v___x_3478_ = lean_array_fset(v_vs_3458_, v_x_3454_, v_x_3456_);
                        leanh::lean_dec(v_x_3454_);
                        if v_isShared_3461_ == 0 {
                            leanh::lean_ctor_set(v___x_3460_, 1, v___x_3478_);
                            leanh::lean_ctor_set(v___x_3460_, 0, v___x_3477_);
                            v___x_3480_ = v___x_3460_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3481_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3481_, 0, v___x_3477_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3481_, 1, v___x_3478_);
                            v___x_3480_ = v_reuseFailAlloc_3481_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3467_;
            }
            3 => {
                v___x_3473_ = leanh::lean_unsigned_to_nat(1);
                v___x_3474_ = lean_nat_add(v_x_3454_, v___x_3473_);
                leanh::lean_dec(v_x_3454_);
                v_x_3453_ = v___x_3472_;
                v_x_3454_ = v___x_3474_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3480_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15___redArg(
    mut v_n_3483_: *mut leanh::LeanObject,
    mut v_k_3484_: *mut leanh::LeanObject,
    mut v_v_3485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3486_ = leanh::lean_unsigned_to_nat(0);
    v___x_3487_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15_spec__17___redArg(v_n_3483_, v___x_3486_, v_k_3484_, v_v_3485_);
    return v___x_3487_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__0()
-> usize {
    let mut v___x_3488_: usize = 0;
    let mut v___x_3489_: usize = 0;
    let mut v___x_3490_: usize = 0;
    v___x_3488_ = 5usize;
    v___x_3489_ = 1usize;
    v___x_3490_ = lean_usize_shift_left(v___x_3489_, v___x_3488_);
    return v___x_3490_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__1()
-> usize {
    let mut v___x_3491_: usize = 0;
    let mut v___x_3492_: usize = 0;
    let mut v___x_3493_: usize = 0;
    v___x_3491_ = 1usize;
    v___x_3492_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__0);
    v___x_3493_ = lean_usize_sub(v___x_3492_, v___x_3491_);
    return v___x_3493_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3494_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3494_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(
    mut v_x_3495_: *mut leanh::LeanObject,
    mut v_x_3496_: usize,
    mut v_x_3497_: usize,
    mut v_x_3498_: *mut leanh::LeanObject,
    mut v_x_3499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: usize = 0;
    let mut v___x_3502_: usize = 0;
    let mut v___x_3503_: usize = 0;
    let mut v___x_3504_: usize = 0;
    let mut v_j_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: u8 = 0;
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3510_: u8 = 0;
    let mut v_v_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3524_: u8 = 0;
    let mut v___x_3525_: u8 = 0;
    let mut v___x_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3531_: u8 = 0;
    let mut v_node_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3535_: u8 = 0;
    let mut v___x_3536_: usize = 0;
    let mut v___x_3537_: usize = 0;
    let mut v___x_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3542_: u8 = 0;
    let mut v___x_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3544_: u8 = 0;
    let mut v_unused_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3550_: u8 = 0;
    let mut v___x_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3555_: u8 = 0;
    let mut v_ks_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: usize = 0;
    let mut v___x_3562_: u8 = 0;
    let mut v___x_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: u8 = 0;
    let mut v_reuseFailAlloc_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3567_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3495_) == 0 {
                    v_es_3500_ = leanh::lean_ctor_get(v_x_3495_, 0);
                    v___x_3501_ = 5usize;
                    v___x_3502_ = 1usize;
                    v___x_3503_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__1);
                    v___x_3504_ = lean_usize_land(v_x_3496_, v___x_3503_);
                    v_j_3505_ = lean_usize_to_nat(v___x_3504_);
                    v___x_3506_ = lean_array_get_size(v_es_3500_);
                    v___x_3507_ = lean_nat_dec_lt(v_j_3505_, v___x_3506_);
                    if v___x_3507_ == 0 {
                        leanh::lean_dec(v_j_3505_);
                        leanh::lean_dec(v_x_3499_);
                        leanh::lean_dec(v_x_3498_);
                        return v_x_3495_;
                    } else {
                        leanh::lean_inc_ref(v_es_3500_);
                        v_isSharedCheck_3544_ = (!leanh::lean_is_exclusive(v_x_3495_)) as u8;
                        if v_isSharedCheck_3544_ == 0 {
                            v_unused_3545_ = leanh::lean_ctor_get(v_x_3495_, 0);
                            leanh::lean_dec(v_unused_3545_);
                            v___x_3509_ = v_x_3495_;
                            v_isShared_3510_ = v_isSharedCheck_3544_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_3495_);
                            v___x_3509_ = leanh::lean_box(0);
                            v_isShared_3510_ = v_isSharedCheck_3544_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3546_ = leanh::lean_ctor_get(v_x_3495_, 0);
                    v_vs_3547_ = leanh::lean_ctor_get(v_x_3495_, 1);
                    v_isSharedCheck_3567_ = (!leanh::lean_is_exclusive(v_x_3495_)) as u8;
                    if v_isSharedCheck_3567_ == 0 {
                        v___x_3549_ = v_x_3495_;
                        v_isShared_3550_ = v_isSharedCheck_3567_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_3547_);
                        leanh::lean_inc(v_ks_3546_);
                        leanh::lean_dec(v_x_3495_);
                        v___x_3549_ = leanh::lean_box(0);
                        v_isShared_3550_ = v_isSharedCheck_3567_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3511_ = lean_array_fget(v_es_3500_, v_j_3505_);
                v___x_3512_ = leanh::lean_box(0);
                v_xs_x27_3513_ = lean_array_fset(v_es_3500_, v_j_3505_, v___x_3512_);
                match leanh::lean_obj_tag(v_v_3511_) {
                    0 => {
                        v_key_3520_ = leanh::lean_ctor_get(v_v_3511_, 0);
                        v_val_3521_ = leanh::lean_ctor_get(v_v_3511_, 1);
                        v_isSharedCheck_3531_ = (!leanh::lean_is_exclusive(v_v_3511_)) as u8;
                        if v_isSharedCheck_3531_ == 0 {
                            v___x_3523_ = v_v_3511_;
                            v_isShared_3524_ = v_isSharedCheck_3531_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3521_);
                            leanh::lean_inc(v_key_3520_);
                            leanh::lean_dec(v_v_3511_);
                            v___x_3523_ = leanh::lean_box(0);
                            v_isShared_3524_ = v_isSharedCheck_3531_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3532_ = leanh::lean_ctor_get(v_v_3511_, 0);
                        v_isSharedCheck_3542_ = (!leanh::lean_is_exclusive(v_v_3511_)) as u8;
                        if v_isSharedCheck_3542_ == 0 {
                            v___x_3534_ = v_v_3511_;
                            v_isShared_3535_ = v_isSharedCheck_3542_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_3532_);
                            leanh::lean_dec(v_v_3511_);
                            v___x_3534_ = leanh::lean_box(0);
                            v_isShared_3535_ = v_isSharedCheck_3542_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3543_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3543_, 0, v_x_3498_);
                        leanh::lean_ctor_set(v___x_3543_, 1, v_x_3499_);
                        v___y_3515_ = v___x_3543_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3516_ = lean_array_fset(v_xs_x27_3513_, v_j_3505_, v___y_3515_);
                leanh::lean_dec(v_j_3505_);
                if v_isShared_3510_ == 0 {
                    leanh::lean_ctor_set(v___x_3509_, 0, v___x_3516_);
                    v___x_3518_ = v___x_3509_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3519_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3519_, 0, v___x_3516_);
                    v___x_3518_ = v_reuseFailAlloc_3519_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3518_;
            }
            4 => {
                v___x_3525_ = l_Lean_instBEqMVarId_beq(v_x_3498_, v_key_3520_);
                if v___x_3525_ == 0 {
                    leanh::lean_del_object(v___x_3523_);
                    v___x_3526_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3520_,
                        v_val_3521_,
                        v_x_3498_,
                        v_x_3499_,
                    );
                    v___x_3527_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3527_, 0, v___x_3526_);
                    v___y_3515_ = v___x_3527_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_3521_);
                    leanh::lean_dec(v_key_3520_);
                    if v_isShared_3524_ == 0 {
                        leanh::lean_ctor_set(v___x_3523_, 1, v_x_3499_);
                        leanh::lean_ctor_set(v___x_3523_, 0, v_x_3498_);
                        v___x_3529_ = v___x_3523_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3530_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_x_3498_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3530_, 1, v_x_3499_);
                        v___x_3529_ = v_reuseFailAlloc_3530_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_3515_ = v___x_3529_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3536_ = lean_usize_shift_right(v_x_3496_, v___x_3501_);
                v___x_3537_ = lean_usize_add(v_x_3497_, v___x_3502_);
                v___x_3538_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(v_node_3532_, v___x_3536_, v___x_3537_, v_x_3498_, v_x_3499_);
                if v_isShared_3535_ == 0 {
                    leanh::lean_ctor_set(v___x_3534_, 0, v___x_3538_);
                    v___x_3540_ = v___x_3534_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3541_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3538_);
                    v___x_3540_ = v_reuseFailAlloc_3541_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3515_ = v___x_3540_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3550_ == 0 {
                    v___x_3552_ = v___x_3549_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3566_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_ks_3546_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3566_, 1, v_vs_3547_);
                    v___x_3552_ = v_reuseFailAlloc_3566_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3553_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15___redArg(v___x_3552_, v_x_3498_, v_x_3499_);
                v___x_3561_ = 7usize;
                v___x_3562_ = lean_usize_dec_le(v___x_3561_, v_x_3497_);
                if v___x_3562_ == 0 {
                    v___x_3563_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3553_);
                    v___x_3564_ = leanh::lean_unsigned_to_nat(4);
                    v___x_3565_ = lean_nat_dec_lt(v___x_3563_, v___x_3564_);
                    leanh::lean_dec(v___x_3563_);
                    v___y_3555_ = v___x_3565_;
                    state = 10;
                    continue;
                } else {
                    v___y_3555_ = v___x_3562_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3555_ == 0 {
                    v_ks_3556_ = leanh::lean_ctor_get(v_newNode_3553_, 0);
                    leanh::lean_inc_ref(v_ks_3556_);
                    v_vs_3557_ = leanh::lean_ctor_get(v_newNode_3553_, 1);
                    leanh::lean_inc_ref(v_vs_3557_);
                    leanh::lean_dec_ref(v_newNode_3553_);
                    v___x_3558_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3559_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__2);
                    v___x_3560_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___redArg(v_x_3497_, v_ks_3556_, v_vs_3557_, v___x_3558_, v___x_3559_);
                    leanh::lean_dec_ref(v_vs_3557_);
                    leanh::lean_dec_ref(v_ks_3556_);
                    return v___x_3560_;
                } else {
                    return v_newNode_3553_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___redArg(
    mut v_depth_3568_: usize,
    mut v_keys_3569_: *mut leanh::LeanObject,
    mut v_vals_3570_: *mut leanh::LeanObject,
    mut v_i_3571_: *mut leanh::LeanObject,
    mut v_entries_3572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: u8 = 0;
    let mut v_k_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: u64 = 0;
    let mut v_h_3578_: usize = 0;
    let mut v___x_3579_: usize = 0;
    let mut v___x_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: usize = 0;
    let mut v___x_3582_: usize = 0;
    let mut v___x_3583_: usize = 0;
    let mut v_h_3584_: usize = 0;
    let mut v___x_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3573_ = lean_array_get_size(v_keys_3569_);
                v___x_3574_ = lean_nat_dec_lt(v_i_3571_, v___x_3573_);
                if v___x_3574_ == 0 {
                    leanh::lean_dec(v_i_3571_);
                    return v_entries_3572_;
                } else {
                    v_k_3575_ = lean_array_fget_borrowed(v_keys_3569_, v_i_3571_);
                    v_v_3576_ = lean_array_fget_borrowed(v_vals_3570_, v_i_3571_);
                    v___x_3577_ = l_Lean_instHashableMVarId_hash(v_k_3575_);
                    v_h_3578_ = lean_uint64_to_usize(v___x_3577_);
                    v___x_3579_ = 5usize;
                    v___x_3580_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3581_ = 1usize;
                    v___x_3582_ = lean_usize_sub(v_depth_3568_, v___x_3581_);
                    v___x_3583_ = lean_usize_mul(v___x_3579_, v___x_3582_);
                    v_h_3584_ = lean_usize_shift_right(v_h_3578_, v___x_3583_);
                    v___x_3585_ = lean_nat_add(v_i_3571_, v___x_3580_);
                    leanh::lean_dec(v_i_3571_);
                    leanh::lean_inc(v_v_3576_);
                    leanh::lean_inc(v_k_3575_);
                    v___x_3586_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(v_entries_3572_, v_h_3584_, v_depth_3568_, v_k_3575_, v_v_3576_);
                    v_i_3571_ = v___x_3585_;
                    v_entries_3572_ = v___x_3586_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___redArg___boxed(
    mut v_depth_3588_: *mut leanh::LeanObject,
    mut v_keys_3589_: *mut leanh::LeanObject,
    mut v_vals_3590_: *mut leanh::LeanObject,
    mut v_i_3591_: *mut leanh::LeanObject,
    mut v_entries_3592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_3593_: usize = 0;
    let mut v_res_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3593_ = leanh::lean_unbox_usize(v_depth_3588_);
    leanh::lean_dec(v_depth_3588_);
    v_res_3594_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___redArg(v_depth_boxed_3593_, v_keys_3589_, v_vals_3590_, v_i_3591_, v_entries_3592_);
    leanh::lean_dec_ref(v_vals_3590_);
    leanh::lean_dec_ref(v_keys_3589_);
    return v_res_3594_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___boxed(
    mut v_x_3595_: *mut leanh::LeanObject,
    mut v_x_3596_: *mut leanh::LeanObject,
    mut v_x_3597_: *mut leanh::LeanObject,
    mut v_x_3598_: *mut leanh::LeanObject,
    mut v_x_3599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_18004__boxed_3600_: usize = 0;
    let mut v_x_18005__boxed_3601_: usize = 0;
    let mut v_res_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_18004__boxed_3600_ = leanh::lean_unbox_usize(v_x_3596_);
    leanh::lean_dec(v_x_3596_);
    v_x_18005__boxed_3601_ = leanh::lean_unbox_usize(v_x_3597_);
    leanh::lean_dec(v_x_3597_);
    v_res_3602_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(v_x_3595_, v_x_18004__boxed_3600_, v_x_18005__boxed_3601_, v_x_3598_, v_x_3599_);
    return v_res_3602_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7___redArg(
    mut v_x_3603_: *mut leanh::LeanObject,
    mut v_x_3604_: *mut leanh::LeanObject,
    mut v_x_3605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3606_: u64 = 0;
    let mut v___x_3607_: usize = 0;
    let mut v___x_3608_: usize = 0;
    let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3606_ = l_Lean_instHashableMVarId_hash(v_x_3604_);
    v___x_3607_ = lean_uint64_to_usize(v___x_3606_);
    v___x_3608_ = 1usize;
    v___x_3609_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(v_x_3603_, v___x_3607_, v___x_3608_, v_x_3604_, v_x_3605_);
    return v___x_3609_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___redArg(
    mut v_mvarId_3610_: *mut leanh::LeanObject,
    mut v_val_3611_: *mut leanh::LeanObject,
    mut v___y_3612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3622_: u8 = 0;
    let mut v_depth_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3635_: u8 = 0;
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3646_: u8 = 0;
    let mut v_isSharedCheck_3647_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3614_ = lean_st_ref_take(v___y_3612_);
                v_mctx_3615_ = leanh::lean_ctor_get(v___x_3614_, 0);
                v_cache_3616_ = leanh::lean_ctor_get(v___x_3614_, 1);
                v_zetaDeltaFVarIds_3617_ = leanh::lean_ctor_get(v___x_3614_, 2);
                v_postponed_3618_ = leanh::lean_ctor_get(v___x_3614_, 3);
                v_diag_3619_ = leanh::lean_ctor_get(v___x_3614_, 4);
                v_isSharedCheck_3647_ = (!leanh::lean_is_exclusive(v___x_3614_)) as u8;
                if v_isSharedCheck_3647_ == 0 {
                    v___x_3621_ = v___x_3614_;
                    v_isShared_3622_ = v_isSharedCheck_3647_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_3619_);
                    leanh::lean_inc(v_postponed_3618_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_3617_);
                    leanh::lean_inc(v_cache_3616_);
                    leanh::lean_inc(v_mctx_3615_);
                    leanh::lean_dec(v___x_3614_);
                    v___x_3621_ = leanh::lean_box(0);
                    v_isShared_3622_ = v_isSharedCheck_3647_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_3623_ = leanh::lean_ctor_get(v_mctx_3615_, 0);
                v_levelAssignDepth_3624_ = leanh::lean_ctor_get(v_mctx_3615_, 1);
                v_lmvarCounter_3625_ = leanh::lean_ctor_get(v_mctx_3615_, 2);
                v_mvarCounter_3626_ = leanh::lean_ctor_get(v_mctx_3615_, 3);
                v_lDecls_3627_ = leanh::lean_ctor_get(v_mctx_3615_, 4);
                v_decls_3628_ = leanh::lean_ctor_get(v_mctx_3615_, 5);
                v_userNames_3629_ = leanh::lean_ctor_get(v_mctx_3615_, 6);
                v_lAssignment_3630_ = leanh::lean_ctor_get(v_mctx_3615_, 7);
                v_eAssignment_3631_ = leanh::lean_ctor_get(v_mctx_3615_, 8);
                v_dAssignment_3632_ = leanh::lean_ctor_get(v_mctx_3615_, 9);
                v_isSharedCheck_3646_ = (!leanh::lean_is_exclusive(v_mctx_3615_)) as u8;
                if v_isSharedCheck_3646_ == 0 {
                    v___x_3634_ = v_mctx_3615_;
                    v_isShared_3635_ = v_isSharedCheck_3646_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_dAssignment_3632_);
                    leanh::lean_inc(v_eAssignment_3631_);
                    leanh::lean_inc(v_lAssignment_3630_);
                    leanh::lean_inc(v_userNames_3629_);
                    leanh::lean_inc(v_decls_3628_);
                    leanh::lean_inc(v_lDecls_3627_);
                    leanh::lean_inc(v_mvarCounter_3626_);
                    leanh::lean_inc(v_lmvarCounter_3625_);
                    leanh::lean_inc(v_levelAssignDepth_3624_);
                    leanh::lean_inc(v_depth_3623_);
                    leanh::lean_dec(v_mctx_3615_);
                    v___x_3634_ = leanh::lean_box(0);
                    v_isShared_3635_ = v_isSharedCheck_3646_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3636_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7___redArg(v_eAssignment_3631_, v_mvarId_3610_, v_val_3611_);
                if v_isShared_3635_ == 0 {
                    leanh::lean_ctor_set(v___x_3634_, 8, v___x_3636_);
                    v___x_3638_ = v___x_3634_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3645_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_depth_3623_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3645_,
                        1,
                        v_levelAssignDepth_3624_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3645_, 2, v_lmvarCounter_3625_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3645_, 3, v_mvarCounter_3626_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3645_, 4, v_lDecls_3627_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3645_, 5, v_decls_3628_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3645_, 6, v_userNames_3629_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3645_, 7, v_lAssignment_3630_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3645_, 8, v___x_3636_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3645_, 9, v_dAssignment_3632_);
                    v___x_3638_ = v_reuseFailAlloc_3645_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3622_ == 0 {
                    leanh::lean_ctor_set(v___x_3621_, 0, v___x_3638_);
                    v___x_3640_ = v___x_3621_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3644_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3638_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3644_, 1, v_cache_3616_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3644_,
                        2,
                        v_zetaDeltaFVarIds_3617_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3644_, 3, v_postponed_3618_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3644_, 4, v_diag_3619_);
                    v___x_3640_ = v_reuseFailAlloc_3644_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3641_ = lean_st_ref_set(v___y_3612_, v___x_3640_);
                v___x_3642_ = leanh::lean_box(0);
                v___x_3643_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3643_, 0, v___x_3642_);
                return v___x_3643_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___redArg___boxed(
    mut v_mvarId_3648_: *mut leanh::LeanObject,
    mut v_val_3649_: *mut leanh::LeanObject,
    mut v___y_3650_: *mut leanh::LeanObject,
    mut v___y_3651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3652_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___redArg(
            v_mvarId_3648_,
            v_val_3649_,
            v___y_3650_,
        );
    leanh::lean_dec(v___y_3650_);
    return v_res_3652_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__1(
    mut v___x_3653_: *mut leanh::LeanObject,
    mut v_snd_3654_: *mut leanh::LeanObject,
    mut v_a_3655_: *mut leanh::LeanObject,
    mut v_fst_3656_: *mut leanh::LeanObject,
    mut v___y_3657_: *mut leanh::LeanObject,
    mut v___y_3658_: *mut leanh::LeanObject,
    mut v___y_3659_: *mut leanh::LeanObject,
    mut v___y_3660_: *mut leanh::LeanObject,
    mut v___y_3661_: *mut leanh::LeanObject,
    mut v___y_3662_: *mut leanh::LeanObject,
    mut v___y_3663_: *mut leanh::LeanObject,
    mut v___y_3664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3677_: u8 = 0;
    let mut v___x_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3681_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3666_ = lean_st_mk_ref(v___x_3653_);
                leanh::lean_inc(v___x_3666_);
                v___f_3667_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__0___boxed
                        as *mut core::ffi::c_void,
                    12,
                    1,
                );
                leanh::lean_closure_set(v___f_3667_, 0, v___x_3666_);
                v___x_3668_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore(
                    v_snd_3654_,
                    v_a_3655_,
                    v___f_3667_,
                    v___y_3657_,
                    v___y_3658_,
                    v___y_3659_,
                    v___y_3660_,
                    v___y_3661_,
                    v___y_3662_,
                    v___y_3663_,
                    v___y_3664_,
                );
                if leanh::lean_obj_tag(v___x_3668_) == 0 {
                    v_a_3669_ = leanh::lean_ctor_get(v___x_3668_, 0);
                    leanh::lean_inc(v_a_3669_);
                    leanh::lean_dec_ref_known(v___x_3668_, 1);
                    v___x_3670_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___redArg(v_fst_3656_, v_a_3669_, v___y_3662_);
                    leanh::lean_dec_ref(v___x_3670_);
                    v___x_3671_ = lean_st_ref_get(v___x_3666_);
                    leanh::lean_dec(v___x_3666_);
                    v___x_3672_ = lean_array_to_list(v___x_3671_);
                    v___x_3673_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                        v___x_3672_,
                        v___y_3658_,
                        v___y_3661_,
                        v___y_3662_,
                        v___y_3663_,
                        v___y_3664_,
                    );
                    return v___x_3673_;
                } else {
                    leanh::lean_dec(v___x_3666_);
                    leanh::lean_dec(v_fst_3656_);
                    v_a_3674_ = leanh::lean_ctor_get(v___x_3668_, 0);
                    v_isSharedCheck_3681_ = (!leanh::lean_is_exclusive(v___x_3668_)) as u8;
                    if v_isSharedCheck_3681_ == 0 {
                        v___x_3676_ = v___x_3668_;
                        v_isShared_3677_ = v_isSharedCheck_3681_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3674_);
                        leanh::lean_dec(v___x_3668_);
                        v___x_3676_ = leanh::lean_box(0);
                        v_isShared_3677_ = v_isSharedCheck_3681_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3677_ == 0 {
                    v___x_3679_ = v___x_3676_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3680_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_a_3674_);
                    v___x_3679_ = v_reuseFailAlloc_3680_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3679_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__1___boxed(
    mut v___x_3682_: *mut leanh::LeanObject,
    mut v_snd_3683_: *mut leanh::LeanObject,
    mut v_a_3684_: *mut leanh::LeanObject,
    mut v_fst_3685_: *mut leanh::LeanObject,
    mut v___y_3686_: *mut leanh::LeanObject,
    mut v___y_3687_: *mut leanh::LeanObject,
    mut v___y_3688_: *mut leanh::LeanObject,
    mut v___y_3689_: *mut leanh::LeanObject,
    mut v___y_3690_: *mut leanh::LeanObject,
    mut v___y_3691_: *mut leanh::LeanObject,
    mut v___y_3692_: *mut leanh::LeanObject,
    mut v___y_3693_: *mut leanh::LeanObject,
    mut v___y_3694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3695_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__1(
        v___x_3682_,
        v_snd_3683_,
        v_a_3684_,
        v_fst_3685_,
        v___y_3686_,
        v___y_3687_,
        v___y_3688_,
        v___y_3689_,
        v___y_3690_,
        v___y_3691_,
        v___y_3692_,
        v___y_3693_,
    );
    leanh::lean_dec(v___y_3693_);
    leanh::lean_dec_ref(v___y_3692_);
    leanh::lean_dec(v___y_3691_);
    leanh::lean_dec_ref(v___y_3690_);
    leanh::lean_dec(v___y_3689_);
    leanh::lean_dec_ref(v___y_3688_);
    leanh::lean_dec(v___y_3687_);
    leanh::lean_dec_ref(v___y_3686_);
    return v_res_3695_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___redArg(
    mut v_ref_3696_: *mut leanh::LeanObject,
    mut v_msg_3697_: *mut leanh::LeanObject,
    mut v___y_3698_: *mut leanh::LeanObject,
    mut v___y_3699_: *mut leanh::LeanObject,
    mut v___y_3700_: *mut leanh::LeanObject,
    mut v___y_3701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3715_: u8 = 0;
    let mut v_cancelTk_x3f_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3717_: u8 = 0;
    let mut v_inheritedTraceOptions_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_3703_ = leanh::lean_ctor_get(v___y_3700_, 0);
    v_fileMap_3704_ = leanh::lean_ctor_get(v___y_3700_, 1);
    v_options_3705_ = leanh::lean_ctor_get(v___y_3700_, 2);
    v_currRecDepth_3706_ = leanh::lean_ctor_get(v___y_3700_, 3);
    v_maxRecDepth_3707_ = leanh::lean_ctor_get(v___y_3700_, 4);
    v_ref_3708_ = leanh::lean_ctor_get(v___y_3700_, 5);
    v_currNamespace_3709_ = leanh::lean_ctor_get(v___y_3700_, 6);
    v_openDecls_3710_ = leanh::lean_ctor_get(v___y_3700_, 7);
    v_initHeartbeats_3711_ = leanh::lean_ctor_get(v___y_3700_, 8);
    v_maxHeartbeats_3712_ = leanh::lean_ctor_get(v___y_3700_, 9);
    v_quotContext_3713_ = leanh::lean_ctor_get(v___y_3700_, 10);
    v_currMacroScope_3714_ = leanh::lean_ctor_get(v___y_3700_, 11);
    v_diag_3715_ = leanh::lean_ctor_get_uint8(
        v___y_3700_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3716_ = leanh::lean_ctor_get(v___y_3700_, 12);
    v_suppressElabErrors_3717_ = leanh::lean_ctor_get_uint8(
        v___y_3700_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3718_ = leanh::lean_ctor_get(v___y_3700_, 13);
    v_ref_3719_ = l_Lean_replaceRef(v_ref_3696_, v_ref_3708_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_3718_);
    leanh::lean_inc(v_cancelTk_x3f_3716_);
    leanh::lean_inc(v_currMacroScope_3714_);
    leanh::lean_inc(v_quotContext_3713_);
    leanh::lean_inc(v_maxHeartbeats_3712_);
    leanh::lean_inc(v_initHeartbeats_3711_);
    leanh::lean_inc(v_openDecls_3710_);
    leanh::lean_inc(v_currNamespace_3709_);
    leanh::lean_inc(v_maxRecDepth_3707_);
    leanh::lean_inc(v_currRecDepth_3706_);
    leanh::lean_inc_ref(v_options_3705_);
    leanh::lean_inc_ref(v_fileMap_3704_);
    leanh::lean_inc_ref(v_fileName_3703_);
    v___x_3720_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_3720_, 0, v_fileName_3703_);
    leanh::lean_ctor_set(v___x_3720_, 1, v_fileMap_3704_);
    leanh::lean_ctor_set(v___x_3720_, 2, v_options_3705_);
    leanh::lean_ctor_set(v___x_3720_, 3, v_currRecDepth_3706_);
    leanh::lean_ctor_set(v___x_3720_, 4, v_maxRecDepth_3707_);
    leanh::lean_ctor_set(v___x_3720_, 5, v_ref_3719_);
    leanh::lean_ctor_set(v___x_3720_, 6, v_currNamespace_3709_);
    leanh::lean_ctor_set(v___x_3720_, 7, v_openDecls_3710_);
    leanh::lean_ctor_set(v___x_3720_, 8, v_initHeartbeats_3711_);
    leanh::lean_ctor_set(v___x_3720_, 9, v_maxHeartbeats_3712_);
    leanh::lean_ctor_set(v___x_3720_, 10, v_quotContext_3713_);
    leanh::lean_ctor_set(v___x_3720_, 11, v_currMacroScope_3714_);
    leanh::lean_ctor_set(v___x_3720_, 12, v_cancelTk_x3f_3716_);
    leanh::lean_ctor_set(v___x_3720_, 13, v_inheritedTraceOptions_3718_);
    leanh::lean_ctor_set_uint8(
        v___x_3720_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_3715_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_3720_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3717_,
    );
    v___x_3721_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__1___redArg(
            v_msg_3697_,
            v___y_3698_,
            v___y_3699_,
            v___x_3720_,
            v___y_3701_,
        );
    leanh::lean_dec_ref_known(v___x_3720_, 14);
    return v___x_3721_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___redArg___boxed(
    mut v_ref_3722_: *mut leanh::LeanObject,
    mut v_msg_3723_: *mut leanh::LeanObject,
    mut v___y_3724_: *mut leanh::LeanObject,
    mut v___y_3725_: *mut leanh::LeanObject,
    mut v___y_3726_: *mut leanh::LeanObject,
    mut v___y_3727_: *mut leanh::LeanObject,
    mut v___y_3728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3729_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___redArg(v_ref_3722_, v_msg_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
    leanh::lean_dec(v___y_3727_);
    leanh::lean_dec_ref(v___y_3726_);
    leanh::lean_dec(v___y_3725_);
    leanh::lean_dec_ref(v___y_3724_);
    leanh::lean_dec(v_ref_3722_);
    return v_res_3729_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3735_ = l_Lean_maxRecDepthErrorMessage;
    v___x_3736_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3736_, 0, v___x_3735_);
    return v___x_3736_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3737_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__3);
    v___x_3738_ = l_Lean_MessageData_ofFormat(v___x_3737_);
    return v___x_3738_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3739_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__4);
    v___x_3740_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__2;
    v___x_3741_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3741_, 0, v___x_3740_);
    leanh::lean_ctor_set(v___x_3741_, 1, v___x_3739_);
    return v___x_3741_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg(
    mut v_ref_3742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3744_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___closed__5);
    v___x_3745_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3745_, 0, v_ref_3742_);
    leanh::lean_ctor_set(v___x_3745_, 1, v___x_3744_);
    v___x_3746_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3746_, 0, v___x_3745_);
    return v___x_3746_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg___boxed(
    mut v_ref_3747_: *mut leanh::LeanObject,
    mut v___y_3748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3749_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg(v_ref_3747_);
    return v_res_3749_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9___redArg(
    mut v_a_3750_: *mut leanh::LeanObject,
    mut v_x_3751_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: u8 = 0;
    let mut v___x_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3751_) == 0 {
                    v___x_3752_ = leanh::lean_box(0);
                    return v___x_3752_;
                } else {
                    v_key_3753_ = leanh::lean_ctor_get(v_x_3751_, 0);
                    v_value_3754_ = leanh::lean_ctor_get(v_x_3751_, 1);
                    v_tail_3755_ = leanh::lean_ctor_get(v_x_3751_, 2);
                    v___x_3756_ = lean_name_eq(v_key_3753_, v_a_3750_);
                    if v___x_3756_ == 0 {
                        v_x_3751_ = v_tail_3755_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_3754_);
                        v___x_3758_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3758_, 0, v_value_3754_);
                        return v___x_3758_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9___redArg___boxed(
    mut v_a_3759_: *mut leanh::LeanObject,
    mut v_x_3760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3761_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9___redArg(v_a_3759_, v_x_3760_);
    leanh::lean_dec(v_x_3760_);
    leanh::lean_dec(v_a_3759_);
    return v_res_3761_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg___closed__0()
-> u64 {
    let mut v___x_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: u64 = 0;
    v___x_3762_ = leanh::lean_unsigned_to_nat(1723);
    v___x_3763_ = lean_uint64_of_nat(v___x_3762_);
    return v___x_3763_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg(
    mut v_m_3764_: *mut leanh::LeanObject,
    mut v_a_3765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3769_: u64 = 0;
    let mut v___x_3770_: u64 = 0;
    let mut v___x_3771_: u64 = 0;
    let mut v_fold_3772_: u64 = 0;
    let mut v___x_3773_: u64 = 0;
    let mut v___x_3774_: u64 = 0;
    let mut v___x_3775_: u64 = 0;
    let mut v___x_3776_: usize = 0;
    let mut v___x_3777_: usize = 0;
    let mut v___x_3778_: usize = 0;
    let mut v___x_3779_: usize = 0;
    let mut v___x_3780_: usize = 0;
    let mut v___x_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: u64 = 0;
    let mut v_hash_3784_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_3766_ = leanh::lean_ctor_get(v_m_3764_, 1);
                v___x_3767_ = lean_array_get_size(v_buckets_3766_);
                if leanh::lean_obj_tag(v_a_3765_) == 0 {
                    v___x_3783_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg___closed__0);
                    v___y_3769_ = v___x_3783_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3784_ = leanh::lean_ctor_get_uint64(
                        v_a_3765_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3769_ = v_hash_3784_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3770_ = 32u64;
                v___x_3771_ = lean_uint64_shift_right(v___y_3769_, v___x_3770_);
                v_fold_3772_ = lean_uint64_xor(v___y_3769_, v___x_3771_);
                v___x_3773_ = 16u64;
                v___x_3774_ = lean_uint64_shift_right(v_fold_3772_, v___x_3773_);
                v___x_3775_ = lean_uint64_xor(v_fold_3772_, v___x_3774_);
                v___x_3776_ = lean_uint64_to_usize(v___x_3775_);
                v___x_3777_ = lean_usize_of_nat(v___x_3767_);
                v___x_3778_ = 1usize;
                v___x_3779_ = lean_usize_sub(v___x_3777_, v___x_3778_);
                v___x_3780_ = lean_usize_land(v___x_3776_, v___x_3779_);
                v___x_3781_ = lean_array_uget_borrowed(v_buckets_3766_, v___x_3780_);
                v___x_3782_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9___redArg(v_a_3765_, v___x_3781_);
                return v___x_3782_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg___boxed(
    mut v_m_3785_: *mut leanh::LeanObject,
    mut v_a_3786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3787_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg(v_m_3785_, v_a_3786_);
    leanh::lean_dec(v_a_3786_);
    leanh::lean_dec_ref(v_m_3785_);
    return v_res_3787_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg(
    mut v_keys_3788_: *mut leanh::LeanObject,
    mut v_i_3789_: *mut leanh::LeanObject,
    mut v_k_3790_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: u8 = 0;
    let mut v_k_x27_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: u8 = 0;
    let mut v___x_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3791_ = lean_array_get_size(v_keys_3788_);
                v___x_3792_ = lean_nat_dec_lt(v_i_3789_, v___x_3791_);
                if v___x_3792_ == 0 {
                    leanh::lean_dec(v_i_3789_);
                    return v___x_3792_;
                } else {
                    v_k_x27_3793_ = lean_array_fget_borrowed(v_keys_3788_, v_i_3789_);
                    v___x_3794_ = l_Lean_instBEqExtraModUse_beq(v_k_3790_, v_k_x27_3793_);
                    if v___x_3794_ == 0 {
                        v___x_3795_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3796_ = lean_nat_add(v_i_3789_, v___x_3795_);
                        leanh::lean_dec(v_i_3789_);
                        v_i_3789_ = v___x_3796_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_i_3789_);
                        return v___x_3794_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg___boxed(
    mut v_keys_3798_: *mut leanh::LeanObject,
    mut v_i_3799_: *mut leanh::LeanObject,
    mut v_k_3800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3801_: u8 = 0;
    let mut v_r_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3801_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg(v_keys_3798_, v_i_3799_, v_k_3800_);
    leanh::lean_dec_ref(v_k_3800_);
    leanh::lean_dec_ref(v_keys_3798_);
    v_r_3802_ = leanh::lean_box((v_res_3801_) as usize);
    return v_r_3802_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg(
    mut v_x_3803_: *mut leanh::LeanObject,
    mut v_x_3804_: usize,
    mut v_x_3805_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_es_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: usize = 0;
    let mut v___x_3809_: usize = 0;
    let mut v___x_3810_: usize = 0;
    let mut v_j_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: u8 = 0;
    let mut v_node_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: usize = 0;
    let mut v___x_3818_: u8 = 0;
    let mut v_ks_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3803_) == 0 {
                    v_es_3806_ = leanh::lean_ctor_get(v_x_3803_, 0);
                    v___x_3807_ = leanh::lean_box(2);
                    v___x_3808_ = 5usize;
                    v___x_3809_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg___closed__1);
                    v___x_3810_ = lean_usize_land(v_x_3804_, v___x_3809_);
                    v_j_3811_ = lean_usize_to_nat(v___x_3810_);
                    v___x_3812_ = lean_array_get_borrowed(v___x_3807_, v_es_3806_, v_j_3811_);
                    leanh::lean_dec(v_j_3811_);
                    match leanh::lean_obj_tag(v___x_3812_) {
                        0 => {
                            v_key_3813_ = leanh::lean_ctor_get(v___x_3812_, 0);
                            v___x_3814_ = l_Lean_instBEqExtraModUse_beq(v_x_3805_, v_key_3813_);
                            return v___x_3814_;
                        }
                        1 => {
                            v_node_3815_ = leanh::lean_ctor_get(v___x_3812_, 0);
                            v___x_3816_ = lean_usize_shift_right(v_x_3804_, v___x_3808_);
                            v_x_3803_ = v_node_3815_;
                            v_x_3804_ = v___x_3816_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3818_ = 0;
                            return v___x_3818_;
                        }
                    }
                } else {
                    v_ks_3819_ = leanh::lean_ctor_get(v_x_3803_, 0);
                    v___x_3820_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3821_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg(v_ks_3819_, v___x_3820_, v_x_3805_);
                    return v___x_3821_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg___boxed(
    mut v_x_3822_: *mut leanh::LeanObject,
    mut v_x_3823_: *mut leanh::LeanObject,
    mut v_x_3824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_18437__boxed_3825_: usize = 0;
    let mut v_res_3826_: u8 = 0;
    let mut v_r_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_18437__boxed_3825_ = leanh::lean_unbox_usize(v_x_3823_);
    leanh::lean_dec(v_x_3823_);
    v_res_3826_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg(v_x_3822_, v_x_18437__boxed_3825_, v_x_3824_);
    leanh::lean_dec_ref(v_x_3824_);
    leanh::lean_dec_ref(v_x_3822_);
    v_r_3827_ = leanh::lean_box((v_res_3826_) as usize);
    return v_r_3827_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg(
    mut v_x_3828_: *mut leanh::LeanObject,
    mut v_x_3829_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3830_: u64 = 0;
    let mut v___x_3831_: usize = 0;
    let mut v___x_3832_: u8 = 0;
    v___x_3830_ = l_Lean_instHashableExtraModUse_hash(v_x_3829_);
    v___x_3831_ = lean_uint64_to_usize(v___x_3830_);
    v___x_3832_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg(v_x_3828_, v___x_3831_, v_x_3829_);
    return v___x_3832_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg___boxed(
    mut v_x_3833_: *mut leanh::LeanObject,
    mut v_x_3834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3835_: u8 = 0;
    let mut v_r_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3835_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg(v_x_3833_, v_x_3834_);
    leanh::lean_dec_ref(v_x_3834_);
    leanh::lean_dec_ref(v_x_3833_);
    v_r_3836_ = leanh::lean_box((v_res_3835_) as usize);
    return v_r_3836_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3839_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__1;
    v___x_3840_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__0;
    v___x_3841_ = l_Lean_PersistentHashMap_empty(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3840_,
        v___x_3839_,
    );
    return v___x_3841_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3842_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3842_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3843_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__3_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__3);
    v___x_3844_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3844_, 0, v___x_3843_);
    return v___x_3844_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3845_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4);
    v___x_3846_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3846_, 0, v___x_3845_);
    leanh::lean_ctor_set(v___x_3846_, 1, v___x_3845_);
    return v___x_3846_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3847_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__4);
    v___x_3848_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_3848_, 0, v___x_3847_);
    leanh::lean_ctor_set(v___x_3848_, 1, v___x_3847_);
    leanh::lean_ctor_set(v___x_3848_, 2, v___x_3847_);
    leanh::lean_ctor_set(v___x_3848_, 3, v___x_3847_);
    leanh::lean_ctor_set(v___x_3848_, 4, v___x_3847_);
    leanh::lean_ctor_set(v___x_3848_, 5, v___x_3847_);
    return v___x_3848_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3853_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__9;
    v___x_3854_ = l_Lean_stringToMessageData(v___x_3853_);
    return v___x_3854_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3856_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__11;
    v___x_3857_ = l_Lean_stringToMessageData(v___x_3856_);
    return v___x_3857_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3858_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg___closed__1;
    v___x_3859_ = l_Lean_stringToMessageData(v___x_3858_);
    return v___x_3859_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__14()
-> *mut leanh::LeanObject {
    let mut v_cls_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cls_3860_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__8;
    v___x_3861_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17;
    v___x_3862_ = l_Lean_Name_append(v___x_3861_, v_cls_3860_);
    return v___x_3862_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3864_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__15;
    v___x_3865_ = l_Lean_stringToMessageData(v___x_3864_);
    return v___x_3865_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3867_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__17;
    v___x_3868_ = l_Lean_stringToMessageData(v___x_3867_);
    return v___x_3868_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg(
    mut v_mod_3873_: *mut leanh::LeanObject,
    mut v_isMeta_3874_: u8,
    mut v_hint_3875_: *mut leanh::LeanObject,
    mut v___y_3876_: *mut leanh::LeanObject,
    mut v___y_3877_: *mut leanh::LeanObject,
    mut v___y_3878_: *mut leanh::LeanObject,
    mut v___y_3879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_3883_: u8 = 0;
    let mut v___x_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3906_: u8 = 0;
    let mut v_asyncMode_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3920_: u8 = 0;
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3928_: u8 = 0;
    let mut v_unused_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3931_: u8 = 0;
    let mut v_unused_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: u8 = 0;
    let mut v_options_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3936_: u8 = 0;
    let mut v_inheritedTraceOptions_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: u8 = 0;
    let mut v___x_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: u8 = 0;
    let mut v___x_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3881_ = lean_st_ref_get(v___y_3879_);
                v_env_3882_ = leanh::lean_ctor_get(v___x_3881_, 0);
                leanh::lean_inc_ref(v_env_3882_);
                leanh::lean_dec(v___x_3881_);
                v_isExporting_3883_ = leanh::lean_ctor_get_uint8(
                    v_env_3882_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                leanh::lean_dec_ref(v_env_3882_);
                v___x_3884_ = lean_st_ref_get(v___y_3879_);
                v_env_3885_ = leanh::lean_ctor_get(v___x_3884_, 0);
                leanh::lean_inc_ref(v_env_3885_);
                leanh::lean_dec(v___x_3884_);
                v___x_3886_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__2);
                leanh::lean_inc(v_mod_3873_);
                v_entry_3887_ = leanh::lean_alloc_ctor(0, 1, (2) as u32);
                leanh::lean_ctor_set(v_entry_3887_, 0, v_mod_3873_);
                leanh::lean_ctor_set_uint8(
                    v_entry_3887_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_isExporting_3883_,
                );
                leanh::lean_ctor_set_uint8(
                    v_entry_3887_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                    v_isMeta_3874_,
                );
                v___x_3888_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_3889_ = leanh::lean_box(1);
                v___x_3890_ = leanh::lean_box(0);
                v___x_3933_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_3886_,
                    v___x_3888_,
                    v_env_3885_,
                    v___x_3889_,
                    v___x_3890_,
                );
                v___x_3934_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg(v___x_3933_, v_entry_3887_);
                leanh::lean_dec(v___x_3933_);
                if v___x_3934_ == 0 {
                    v_options_3935_ = leanh::lean_ctor_get(v___y_3878_, 2);
                    v_hasTrace_3936_ = leanh::lean_ctor_get_uint8(
                        v_options_3935_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_3936_ == 0 {
                        leanh::lean_dec(v_hint_3875_);
                        leanh::lean_dec(v_mod_3873_);
                        v___y_3892_ = v___y_3877_;
                        v___y_3893_ = v___y_3879_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_3937_ =
                            leanh::lean_ctor_get(v___y_3878_, 13);
                        v_cls_3938_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__8;
                        v___x_3958_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__14_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__14);
                        v___x_3959_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_3937_,
                            v_options_3935_,
                            v___x_3958_,
                        );
                        if v___x_3959_ == 0 {
                            leanh::lean_dec(v_hint_3875_);
                            leanh::lean_dec(v_mod_3873_);
                            v___y_3892_ = v___y_3877_;
                            v___y_3893_ = v___y_3879_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3960_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__16), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__16_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__16);
                            if v_isExporting_3883_ == 0 {
                                v___x_3969_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__21;
                                v___y_3962_ = v___x_3969_;
                                state = 8;
                                continue;
                            } else {
                                v___x_3970_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__22;
                                v___y_3962_ = v___x_3970_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref_known(v_entry_3887_, 1);
                    leanh::lean_dec(v_hint_3875_);
                    leanh::lean_dec(v_mod_3873_);
                    v___x_3971_ = leanh::lean_box(0);
                    v___x_3972_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3972_, 0, v___x_3971_);
                    return v___x_3972_;
                }
            }
            1 => {
                v___x_3894_ = lean_st_ref_take(v___y_3893_);
                v_toEnvExtension_3895_ = leanh::lean_ctor_get(v___x_3888_, 0);
                v_env_3896_ = leanh::lean_ctor_get(v___x_3894_, 0);
                v_nextMacroScope_3897_ = leanh::lean_ctor_get(v___x_3894_, 1);
                v_ngen_3898_ = leanh::lean_ctor_get(v___x_3894_, 2);
                v_auxDeclNGen_3899_ = leanh::lean_ctor_get(v___x_3894_, 3);
                v_traceState_3900_ = leanh::lean_ctor_get(v___x_3894_, 4);
                v_messages_3901_ = leanh::lean_ctor_get(v___x_3894_, 6);
                v_infoState_3902_ = leanh::lean_ctor_get(v___x_3894_, 7);
                v_snapshotTasks_3903_ = leanh::lean_ctor_get(v___x_3894_, 8);
                v_isSharedCheck_3931_ = (!leanh::lean_is_exclusive(v___x_3894_)) as u8;
                if v_isSharedCheck_3931_ == 0 {
                    v_unused_3932_ = leanh::lean_ctor_get(v___x_3894_, 5);
                    leanh::lean_dec(v_unused_3932_);
                    v___x_3905_ = v___x_3894_;
                    v_isShared_3906_ = v_isSharedCheck_3931_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3903_);
                    leanh::lean_inc(v_infoState_3902_);
                    leanh::lean_inc(v_messages_3901_);
                    leanh::lean_inc(v_traceState_3900_);
                    leanh::lean_inc(v_auxDeclNGen_3899_);
                    leanh::lean_inc(v_ngen_3898_);
                    leanh::lean_inc(v_nextMacroScope_3897_);
                    leanh::lean_inc(v_env_3896_);
                    leanh::lean_dec(v___x_3894_);
                    v___x_3905_ = leanh::lean_box(0);
                    v_isShared_3906_ = v_isSharedCheck_3931_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_3907_ = leanh::lean_ctor_get(v_toEnvExtension_3895_, 2);
                v___x_3908_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_3888_,
                    v_env_3896_,
                    v_entry_3887_,
                    v_asyncMode_3907_,
                    v___x_3890_,
                );
                v___x_3909_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__5), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__5_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__5);
                if v_isShared_3906_ == 0 {
                    leanh::lean_ctor_set(v___x_3905_, 5, v___x_3909_);
                    leanh::lean_ctor_set(v___x_3905_, 0, v___x_3908_);
                    v___x_3911_ = v___x_3905_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3930_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 0, v___x_3908_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 1, v_nextMacroScope_3897_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 2, v_ngen_3898_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 3, v_auxDeclNGen_3899_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 4, v_traceState_3900_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 5, v___x_3909_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 6, v_messages_3901_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 7, v_infoState_3902_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3930_, 8, v_snapshotTasks_3903_);
                    v___x_3911_ = v_reuseFailAlloc_3930_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3912_ = lean_st_ref_set(v___y_3893_, v___x_3911_);
                v___x_3913_ = lean_st_ref_take(v___y_3892_);
                v_mctx_3914_ = leanh::lean_ctor_get(v___x_3913_, 0);
                v_zetaDeltaFVarIds_3915_ = leanh::lean_ctor_get(v___x_3913_, 2);
                v_postponed_3916_ = leanh::lean_ctor_get(v___x_3913_, 3);
                v_diag_3917_ = leanh::lean_ctor_get(v___x_3913_, 4);
                v_isSharedCheck_3928_ = (!leanh::lean_is_exclusive(v___x_3913_)) as u8;
                if v_isSharedCheck_3928_ == 0 {
                    v_unused_3929_ = leanh::lean_ctor_get(v___x_3913_, 1);
                    leanh::lean_dec(v_unused_3929_);
                    v___x_3919_ = v___x_3913_;
                    v_isShared_3920_ = v_isSharedCheck_3928_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_3917_);
                    leanh::lean_inc(v_postponed_3916_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_3915_);
                    leanh::lean_inc(v_mctx_3914_);
                    leanh::lean_dec(v___x_3913_);
                    v___x_3919_ = leanh::lean_box(0);
                    v_isShared_3920_ = v_isSharedCheck_3928_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3921_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__6), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__6_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__6);
                if v_isShared_3920_ == 0 {
                    leanh::lean_ctor_set(v___x_3919_, 1, v___x_3921_);
                    v___x_3923_ = v___x_3919_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3927_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_mctx_3914_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3927_, 1, v___x_3921_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3927_,
                        2,
                        v_zetaDeltaFVarIds_3915_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3927_, 3, v_postponed_3916_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3927_, 4, v_diag_3917_);
                    v___x_3923_ = v_reuseFailAlloc_3927_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3924_ = lean_st_ref_set(v___y_3892_, v___x_3923_);
                v___x_3925_ = leanh::lean_box(0);
                v___x_3926_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3926_, 0, v___x_3925_);
                return v___x_3926_;
            }
            6 => {
                v___x_3942_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3942_, 0, v___y_3940_);
                leanh::lean_ctor_set(v___x_3942_, 1, v___y_3941_);
                v___x_3943_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg(v_cls_3938_, v___x_3942_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_);
                if leanh::lean_obj_tag(v___x_3943_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3943_, 1);
                    v___y_3892_ = v___y_3877_;
                    v___y_3893_ = v___y_3879_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v_entry_3887_, 1);
                    return v___x_3943_;
                }
            }
            7 => {
                leanh::lean_inc_ref(v___y_3946_);
                v___x_3947_ = l_Lean_stringToMessageData(v___y_3946_);
                v___x_3948_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3948_, 0, v___y_3945_);
                leanh::lean_ctor_set(v___x_3948_, 1, v___x_3947_);
                v___x_3949_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__10_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__10);
                v___x_3950_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3950_, 0, v___x_3948_);
                leanh::lean_ctor_set(v___x_3950_, 1, v___x_3949_);
                v___x_3951_ = l_Lean_MessageData_ofName(v_mod_3873_);
                v___x_3952_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3952_, 0, v___x_3950_);
                leanh::lean_ctor_set(v___x_3952_, 1, v___x_3951_);
                v___x_3953_ = l_Lean_Name_isAnonymous(v_hint_3875_);
                if v___x_3953_ == 0 {
                    v___x_3954_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__12);
                    v___x_3955_ = l_Lean_MessageData_ofName(v_hint_3875_);
                    v___x_3956_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3956_, 0, v___x_3954_);
                    leanh::lean_ctor_set(v___x_3956_, 1, v___x_3955_);
                    v___y_3940_ = v___x_3952_;
                    v___y_3941_ = v___x_3956_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_dec(v_hint_3875_);
                    v___x_3957_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__13), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__13_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__13);
                    v___y_3940_ = v___x_3952_;
                    v___y_3941_ = v___x_3957_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                leanh::lean_inc_ref(v___y_3962_);
                v___x_3963_ = l_Lean_stringToMessageData(v___y_3962_);
                v___x_3964_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3964_, 0, v___x_3960_);
                leanh::lean_ctor_set(v___x_3964_, 1, v___x_3963_);
                v___x_3965_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__18), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__18_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__18);
                v___x_3966_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3966_, 0, v___x_3964_);
                leanh::lean_ctor_set(v___x_3966_, 1, v___x_3965_);
                if v_isMeta_3874_ == 0 {
                    v___x_3967_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__19;
                    v___y_3945_ = v___x_3966_;
                    v___y_3946_ = v___x_3967_;
                    state = 7;
                    continue;
                } else {
                    v___x_3968_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___closed__20;
                    v___y_3945_ = v___x_3966_;
                    v___y_3946_ = v___x_3968_;
                    state = 7;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_mod_3973_: *mut leanh::LeanObject,
    mut v_isMeta_3974_: *mut leanh::LeanObject,
    mut v_hint_3975_: *mut leanh::LeanObject,
    mut v___y_3976_: *mut leanh::LeanObject,
    mut v___y_3977_: *mut leanh::LeanObject,
    mut v___y_3978_: *mut leanh::LeanObject,
    mut v___y_3979_: *mut leanh::LeanObject,
    mut v___y_3980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isMeta_boxed_3981_: u8 = 0;
    let mut v_res_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_3981_ = (leanh::lean_unbox(v_isMeta_3974_) as u8);
    v_res_3982_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg(v_mod_3973_, v_isMeta_boxed_3981_, v_hint_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_);
    leanh::lean_dec(v___y_3979_);
    leanh::lean_dec_ref(v___y_3978_);
    leanh::lean_dec(v___y_3977_);
    leanh::lean_dec_ref(v___y_3976_);
    return v_res_3982_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__4(
    mut v___x_3983_: *mut leanh::LeanObject,
    mut v_declName_3984_: *mut leanh::LeanObject,
    mut v_as_3985_: *mut leanh::LeanObject,
    mut v_sz_3986_: usize,
    mut v_i_3987_: usize,
    mut v_b_3988_: *mut leanh::LeanObject,
    mut v___y_3989_: *mut leanh::LeanObject,
    mut v___y_3990_: *mut leanh::LeanObject,
    mut v___y_3991_: *mut leanh::LeanObject,
    mut v___y_3992_: *mut leanh::LeanObject,
    mut v___y_3993_: *mut leanh::LeanObject,
    mut v___y_3994_: *mut leanh::LeanObject,
    mut v___y_3995_: *mut leanh::LeanObject,
    mut v___y_3996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3998_: u8 = 0;
    let mut v___x_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: u8 = 0;
    let mut v___x_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: usize = 0;
    let mut v___x_4011_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3998_ = lean_usize_dec_lt(v_i_3987_, v_sz_3986_);
                if v___x_3998_ == 0 {
                    leanh::lean_dec(v_declName_3984_);
                    v___x_3999_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3999_, 0, v_b_3988_);
                    return v___x_3999_;
                } else {
                    v___x_4000_ = l_Lean_Environment_header(v___x_3983_);
                    v_modules_4001_ = leanh::lean_ctor_get(v___x_4000_, 3);
                    leanh::lean_inc_ref(v_modules_4001_);
                    leanh::lean_dec_ref(v___x_4000_);
                    v___x_4002_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_4003_ = lean_array_uget_borrowed(v_as_3985_, v_i_3987_);
                    v___x_4004_ = lean_array_get(v___x_4002_, v_modules_4001_, v_a_4003_);
                    leanh::lean_dec_ref(v_modules_4001_);
                    v_toImport_4005_ = leanh::lean_ctor_get(v___x_4004_, 0);
                    leanh::lean_inc_ref(v_toImport_4005_);
                    leanh::lean_dec(v___x_4004_);
                    v_module_4006_ = leanh::lean_ctor_get(v_toImport_4005_, 0);
                    leanh::lean_inc(v_module_4006_);
                    leanh::lean_dec_ref(v_toImport_4005_);
                    v___x_4007_ = 0;
                    leanh::lean_inc(v_declName_3984_);
                    v___x_4008_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg(v_module_4006_, v___x_4007_, v_declName_3984_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_);
                    if leanh::lean_obj_tag(v___x_4008_) == 0 {
                        leanh::lean_dec_ref_known(v___x_4008_, 1);
                        v___x_4009_ = leanh::lean_box(0);
                        v___x_4010_ = 1usize;
                        v___x_4011_ = lean_usize_add(v_i_3987_, v___x_4010_);
                        v_i_3987_ = v___x_4011_;
                        v_b_3988_ = v___x_4009_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_declName_3984_);
                        return v___x_4008_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__4___boxed(
    mut v___x_4013_: *mut leanh::LeanObject,
    mut v_declName_4014_: *mut leanh::LeanObject,
    mut v_as_4015_: *mut leanh::LeanObject,
    mut v_sz_4016_: *mut leanh::LeanObject,
    mut v_i_4017_: *mut leanh::LeanObject,
    mut v_b_4018_: *mut leanh::LeanObject,
    mut v___y_4019_: *mut leanh::LeanObject,
    mut v___y_4020_: *mut leanh::LeanObject,
    mut v___y_4021_: *mut leanh::LeanObject,
    mut v___y_4022_: *mut leanh::LeanObject,
    mut v___y_4023_: *mut leanh::LeanObject,
    mut v___y_4024_: *mut leanh::LeanObject,
    mut v___y_4025_: *mut leanh::LeanObject,
    mut v___y_4026_: *mut leanh::LeanObject,
    mut v___y_4027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4028_: usize = 0;
    let mut v_i_boxed_4029_: usize = 0;
    let mut v_res_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4028_ = leanh::lean_unbox_usize(v_sz_4016_);
    leanh::lean_dec(v_sz_4016_);
    v_i_boxed_4029_ = leanh::lean_unbox_usize(v_i_4017_);
    leanh::lean_dec(v_i_4017_);
    v_res_4030_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__4(v___x_4013_, v_declName_4014_, v_as_4015_, v_sz_boxed_4028_, v_i_boxed_4029_, v_b_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
    leanh::lean_dec(v___y_4026_);
    leanh::lean_dec_ref(v___y_4025_);
    leanh::lean_dec(v___y_4024_);
    leanh::lean_dec_ref(v___y_4023_);
    leanh::lean_dec(v___y_4022_);
    leanh::lean_dec_ref(v___y_4021_);
    leanh::lean_dec(v___y_4020_);
    leanh::lean_dec_ref(v___y_4019_);
    leanh::lean_dec_ref(v_as_4015_);
    leanh::lean_dec_ref(v___x_4013_);
    return v_res_4030_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4033_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__1;
    v___x_4034_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__0;
    v___x_4035_ = l_Std_HashMap_instInhabited(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4034_,
        v___x_4033_,
    );
    return v___x_4035_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1(
    mut v_declName_4038_: *mut leanh::LeanObject,
    mut v_isMeta_4039_: u8,
    mut v___y_4040_: *mut leanh::LeanObject,
    mut v___y_4041_: *mut leanh::LeanObject,
    mut v___y_4042_: *mut leanh::LeanObject,
    mut v___y_4043_: *mut leanh::LeanObject,
    mut v___y_4044_: *mut leanh::LeanObject,
    mut v___y_4045_: *mut leanh::LeanObject,
    mut v___y_4046_: *mut leanh::LeanObject,
    mut v___y_4047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4057_: usize = 0;
    let mut v___x_4058_: usize = 0;
    let mut v___x_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4062_: u8 = 0;
    let mut v___x_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4066_: u8 = 0;
    let mut v_unused_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: u8 = 0;
    let mut v___x_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4079_: u8 = 0;
    let mut v_toImport_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: u8 = 0;
    let mut v___x_4091_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4049_ = lean_st_ref_get(v___y_4047_);
                v_env_4053_ = leanh::lean_ctor_get(v___x_4049_, 0);
                leanh::lean_inc_ref(v_env_4053_);
                leanh::lean_dec(v___x_4049_);
                v___x_4068_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4053_, v_declName_4038_);
                if leanh::lean_obj_tag(v___x_4068_) == 0 {
                    leanh::lean_dec_ref(v_env_4053_);
                    leanh::lean_dec(v_declName_4038_);
                    state = 1;
                    continue;
                } else {
                    v_val_4069_ = leanh::lean_ctor_get(v___x_4068_, 0);
                    leanh::lean_inc(v_val_4069_);
                    leanh::lean_dec_ref_known(v___x_4068_, 1);
                    v___x_4070_ = l_Lean_Environment_header(v_env_4053_);
                    v_modules_4071_ = leanh::lean_ctor_get(v___x_4070_, 3);
                    leanh::lean_inc_ref(v_modules_4071_);
                    leanh::lean_dec_ref(v___x_4070_);
                    v___x_4072_ = lean_array_get_size(v_modules_4071_);
                    v___x_4073_ = lean_nat_dec_lt(v_val_4069_, v___x_4072_);
                    if v___x_4073_ == 0 {
                        leanh::lean_dec_ref(v_modules_4071_);
                        leanh::lean_dec(v_val_4069_);
                        leanh::lean_dec_ref(v_env_4053_);
                        leanh::lean_dec(v_declName_4038_);
                        state = 1;
                        continue;
                    } else {
                        v___x_4074_ = lean_st_ref_get(v___y_4047_);
                        v_env_4075_ = leanh::lean_ctor_get(v___x_4074_, 0);
                        leanh::lean_inc_ref(v_env_4075_);
                        leanh::lean_dec(v___x_4074_);
                        v___x_4076_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__2);
                        v___x_4077_ = lean_array_fget(v_modules_4071_, v_val_4069_);
                        leanh::lean_dec(v_val_4069_);
                        leanh::lean_dec_ref(v_modules_4071_);
                        if v_isMeta_4039_ == 0 {
                            leanh::lean_dec_ref(v_env_4075_);
                            v___y_4079_ = v_isMeta_4039_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_declName_4038_);
                            v___x_4090_ = l_Lean_isMarkedMeta(v_env_4075_, v_declName_4038_);
                            if v___x_4090_ == 0 {
                                v___y_4079_ = v_isMeta_4039_;
                                state = 5;
                                continue;
                            } else {
                                v___x_4091_ = 0;
                                v___y_4079_ = v___x_4091_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4051_ = leanh::lean_box(0);
                v___x_4052_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4052_, 0, v___x_4051_);
                return v___x_4052_;
            }
            2 => {
                v___x_4056_ = leanh::lean_box(0);
                v_sz_4057_ = lean_array_size(v___y_4055_);
                v___x_4058_ = 0usize;
                v___x_4059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__4(v_env_4053_, v_declName_4038_, v___y_4055_, v_sz_4057_, v___x_4058_, v___x_4056_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_);
                leanh::lean_dec_ref(v___y_4055_);
                leanh::lean_dec_ref(v_env_4053_);
                if leanh::lean_obj_tag(v___x_4059_) == 0 {
                    v_isSharedCheck_4066_ = (!leanh::lean_is_exclusive(v___x_4059_)) as u8;
                    if v_isSharedCheck_4066_ == 0 {
                        v_unused_4067_ = leanh::lean_ctor_get(v___x_4059_, 0);
                        leanh::lean_dec(v_unused_4067_);
                        v___x_4061_ = v___x_4059_;
                        v_isShared_4062_ = v_isSharedCheck_4066_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_4059_);
                        v___x_4061_ = leanh::lean_box(0);
                        v_isShared_4062_ = v_isSharedCheck_4066_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_4059_;
                }
            }
            3 => {
                if v_isShared_4062_ == 0 {
                    leanh::lean_ctor_set(v___x_4061_, 0, v___x_4056_);
                    v___x_4064_ = v___x_4061_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4065_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4065_, 0, v___x_4056_);
                    v___x_4064_ = v_reuseFailAlloc_4065_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4064_;
            }
            5 => {
                v_toImport_4080_ = leanh::lean_ctor_get(v___x_4077_, 0);
                leanh::lean_inc_ref(v_toImport_4080_);
                leanh::lean_dec(v___x_4077_);
                v_module_4081_ = leanh::lean_ctor_get(v_toImport_4080_, 0);
                leanh::lean_inc(v_module_4081_);
                leanh::lean_dec_ref(v_toImport_4080_);
                leanh::lean_inc(v_declName_4038_);
                v___x_4082_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg(v_module_4081_, v___y_4079_, v_declName_4038_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_);
                if leanh::lean_obj_tag(v___x_4082_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4082_, 1);
                    v___x_4083_ = l_Lean_indirectModUseExt;
                    v___x_4084_ = leanh::lean_box(1);
                    v___x_4085_ = leanh::lean_box(0);
                    leanh::lean_inc_ref(v_env_4053_);
                    v___x_4086_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_4076_,
                        v___x_4083_,
                        v_env_4053_,
                        v___x_4084_,
                        v___x_4085_,
                    );
                    v___x_4087_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg(v___x_4086_, v_declName_4038_);
                    leanh::lean_dec(v___x_4086_);
                    if leanh::lean_obj_tag(v___x_4087_) == 0 {
                        v___x_4088_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___closed__3;
                        v___y_4055_ = v___x_4088_;
                        state = 2;
                        continue;
                    } else {
                        v_val_4089_ = leanh::lean_ctor_get(v___x_4087_, 0);
                        leanh::lean_inc(v_val_4089_);
                        leanh::lean_dec_ref_known(v___x_4087_, 1);
                        v___y_4055_ = v_val_4089_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_env_4053_);
                    leanh::lean_dec(v_declName_4038_);
                    return v___x_4082_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1___boxed(
    mut v_declName_4092_: *mut leanh::LeanObject,
    mut v_isMeta_4093_: *mut leanh::LeanObject,
    mut v___y_4094_: *mut leanh::LeanObject,
    mut v___y_4095_: *mut leanh::LeanObject,
    mut v___y_4096_: *mut leanh::LeanObject,
    mut v___y_4097_: *mut leanh::LeanObject,
    mut v___y_4098_: *mut leanh::LeanObject,
    mut v___y_4099_: *mut leanh::LeanObject,
    mut v___y_4100_: *mut leanh::LeanObject,
    mut v___y_4101_: *mut leanh::LeanObject,
    mut v___y_4102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isMeta_boxed_4103_: u8 = 0;
    let mut v_res_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_4103_ = (leanh::lean_unbox(v_isMeta_4093_) as u8);
    v_res_4104_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1(v_declName_4092_, v_isMeta_boxed_4103_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_);
    leanh::lean_dec(v___y_4101_);
    leanh::lean_dec_ref(v___y_4100_);
    leanh::lean_dec(v___y_4099_);
    leanh::lean_dec_ref(v___y_4098_);
    leanh::lean_dec(v___y_4097_);
    leanh::lean_dec_ref(v___y_4096_);
    leanh::lean_dec(v___y_4095_);
    leanh::lean_dec_ref(v___y_4094_);
    return v_res_4104_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___redArg(
    mut v_as_x27_4105_: *mut leanh::LeanObject,
    mut v_b_4106_: *mut leanh::LeanObject,
    mut v___y_4107_: *mut leanh::LeanObject,
    mut v___y_4108_: *mut leanh::LeanObject,
    mut v___y_4109_: *mut leanh::LeanObject,
    mut v___y_4110_: *mut leanh::LeanObject,
    mut v___y_4111_: *mut leanh::LeanObject,
    mut v___y_4112_: *mut leanh::LeanObject,
    mut v___y_4113_: *mut leanh::LeanObject,
    mut v___y_4114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: u8 = 0;
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_4105_) == 0 {
                    v___x_4116_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4116_, 0, v_b_4106_);
                    return v___x_4116_;
                } else {
                    v_head_4117_ = leanh::lean_ctor_get(v_as_x27_4105_, 0);
                    v_tail_4118_ = leanh::lean_ctor_get(v_as_x27_4105_, 1);
                    v___x_4119_ = 1;
                    leanh::lean_inc(v_head_4117_);
                    v___x_4120_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1(v_head_4117_, v___x_4119_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_);
                    if leanh::lean_obj_tag(v___x_4120_) == 0 {
                        leanh::lean_dec_ref_known(v___x_4120_, 1);
                        v___x_4121_ = leanh::lean_box(0);
                        v_as_x27_4105_ = v_tail_4118_;
                        v_b_4106_ = v___x_4121_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4120_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___redArg___boxed(
    mut v_as_x27_4123_: *mut leanh::LeanObject,
    mut v_b_4124_: *mut leanh::LeanObject,
    mut v___y_4125_: *mut leanh::LeanObject,
    mut v___y_4126_: *mut leanh::LeanObject,
    mut v___y_4127_: *mut leanh::LeanObject,
    mut v___y_4128_: *mut leanh::LeanObject,
    mut v___y_4129_: *mut leanh::LeanObject,
    mut v___y_4130_: *mut leanh::LeanObject,
    mut v___y_4131_: *mut leanh::LeanObject,
    mut v___y_4132_: *mut leanh::LeanObject,
    mut v___y_4133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4134_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___redArg(v_as_x27_4123_, v_b_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
    leanh::lean_dec(v___y_4132_);
    leanh::lean_dec_ref(v___y_4131_);
    leanh::lean_dec(v___y_4130_);
    leanh::lean_dec_ref(v___y_4129_);
    leanh::lean_dec(v___y_4128_);
    leanh::lean_dec_ref(v___y_4127_);
    leanh::lean_dec(v___y_4126_);
    leanh::lean_dec_ref(v___y_4125_);
    leanh::lean_dec(v_as_x27_4123_);
    return v_res_4134_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__3(
    mut v_currNamespace_4135_: *mut leanh::LeanObject,
    mut v___y_4136_: *mut leanh::LeanObject,
    mut v___y_4137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4138_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4138_, 0, v_currNamespace_4135_);
    leanh::lean_ctor_set(v___x_4138_, 1, v___y_4137_);
    return v___x_4138_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__3___boxed(
    mut v_currNamespace_4139_: *mut leanh::LeanObject,
    mut v___y_4140_: *mut leanh::LeanObject,
    mut v___y_4141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4142_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__3(v_currNamespace_4139_, v___y_4140_, v___y_4141_);
    leanh::lean_dec_ref(v___y_4140_);
    return v_res_4142_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__4(
    mut v_env_4143_: *mut leanh::LeanObject,
    mut v_options_4144_: *mut leanh::LeanObject,
    mut v_currNamespace_4145_: *mut leanh::LeanObject,
    mut v_openDecls_4146_: *mut leanh::LeanObject,
    mut v_n_4147_: *mut leanh::LeanObject,
    mut v___y_4148_: *mut leanh::LeanObject,
    mut v___y_4149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4150_ = l_Lean_ResolveName_resolveGlobalName(
        v_env_4143_,
        v_options_4144_,
        v_currNamespace_4145_,
        v_openDecls_4146_,
        v_n_4147_,
    );
    v___x_4151_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4151_, 0, v___x_4150_);
    leanh::lean_ctor_set(v___x_4151_, 1, v___y_4149_);
    return v___x_4151_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__4___boxed(
    mut v_env_4152_: *mut leanh::LeanObject,
    mut v_options_4153_: *mut leanh::LeanObject,
    mut v_currNamespace_4154_: *mut leanh::LeanObject,
    mut v_openDecls_4155_: *mut leanh::LeanObject,
    mut v_n_4156_: *mut leanh::LeanObject,
    mut v___y_4157_: *mut leanh::LeanObject,
    mut v___y_4158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4159_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__4(v_env_4152_, v_options_4153_, v_currNamespace_4154_, v_openDecls_4155_, v_n_4156_, v___y_4157_, v___y_4158_);
    leanh::lean_dec_ref(v___y_4157_);
    leanh::lean_dec_ref(v_options_4153_);
    return v_res_4159_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg(
    mut v_x_4160_: *mut leanh::LeanObject,
    mut v___y_4161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4160_) == 0 {
        let mut v_a_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_4162_ = leanh::lean_ctor_get(v_x_4160_, 0);
        leanh::lean_inc(v_a_4162_);
        v___x_4163_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4163_, 0, v_a_4162_);
        leanh::lean_ctor_set(v___x_4163_, 1, v___y_4161_);
        return v___x_4163_;
    } else {
        let mut v_a_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_4164_ = leanh::lean_ctor_get(v_x_4160_, 0);
        leanh::lean_inc(v_a_4164_);
        v___x_4165_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4165_, 0, v_a_4164_);
        leanh::lean_ctor_set(v___x_4165_, 1, v___y_4161_);
        return v___x_4165_;
    }
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg___boxed(
    mut v_x_4166_: *mut leanh::LeanObject,
    mut v___y_4167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4168_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg(v_x_4166_, v___y_4167_);
    leanh::lean_dec_ref(v_x_4166_);
    return v_res_4168_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__0(
    mut v_env_4169_: *mut leanh::LeanObject,
    mut v_stx_4170_: *mut leanh::LeanObject,
    mut v___y_4171_: *mut leanh::LeanObject,
    mut v___y_4172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4178_: u8 = 0;
    let mut v___x_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4183_: u8 = 0;
    let mut v_unused_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4188_: u8 = 0;
    let mut v_snd_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4194_: u8 = 0;
    let mut v___x_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4199_: u8 = 0;
    let mut v_a_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4204_: u8 = 0;
    let mut v___x_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4212_: u8 = 0;
    let mut v_isSharedCheck_4213_: u8 = 0;
    let mut v_a_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4218_: u8 = 0;
    let mut v___x_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4222_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4173_ = l_Lean_Elab_expandMacroImpl_x3f(
                    v_env_4169_,
                    v_stx_4170_,
                    v___y_4171_,
                    v___y_4172_,
                );
                if leanh::lean_obj_tag(v___x_4173_) == 0 {
                    v_a_4174_ = leanh::lean_ctor_get(v___x_4173_, 0);
                    leanh::lean_inc(v_a_4174_);
                    if leanh::lean_obj_tag(v_a_4174_) == 0 {
                        v_a_4175_ = leanh::lean_ctor_get(v___x_4173_, 1);
                        v_isSharedCheck_4183_ =
                            (!leanh::lean_is_exclusive(v___x_4173_)) as u8;
                        if v_isSharedCheck_4183_ == 0 {
                            v_unused_4184_ = leanh::lean_ctor_get(v___x_4173_, 0);
                            leanh::lean_dec(v_unused_4184_);
                            v___x_4177_ = v___x_4173_;
                            v_isShared_4178_ = v_isSharedCheck_4183_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4175_);
                            leanh::lean_dec(v___x_4173_);
                            v___x_4177_ = leanh::lean_box(0);
                            v_isShared_4178_ = v_isSharedCheck_4183_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_val_4185_ = leanh::lean_ctor_get(v_a_4174_, 0);
                        v_isSharedCheck_4213_ = (!leanh::lean_is_exclusive(v_a_4174_)) as u8;
                        if v_isSharedCheck_4213_ == 0 {
                            v___x_4187_ = v_a_4174_;
                            v_isShared_4188_ = v_isSharedCheck_4213_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_4185_);
                            leanh::lean_dec(v_a_4174_);
                            v___x_4187_ = leanh::lean_box(0);
                            v_isShared_4188_ = v_isSharedCheck_4213_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_4214_ = leanh::lean_ctor_get(v___x_4173_, 0);
                    v_a_4215_ = leanh::lean_ctor_get(v___x_4173_, 1);
                    v_isSharedCheck_4222_ = (!leanh::lean_is_exclusive(v___x_4173_)) as u8;
                    if v_isSharedCheck_4222_ == 0 {
                        v___x_4217_ = v___x_4173_;
                        v_isShared_4218_ = v_isSharedCheck_4222_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4215_);
                        leanh::lean_inc(v_a_4214_);
                        leanh::lean_dec(v___x_4173_);
                        v___x_4217_ = leanh::lean_box(0);
                        v_isShared_4218_ = v_isSharedCheck_4222_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4179_ = leanh::lean_box(0);
                if v_isShared_4178_ == 0 {
                    leanh::lean_ctor_set(v___x_4177_, 0, v___x_4179_);
                    v___x_4181_ = v___x_4177_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4182_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4182_, 0, v___x_4179_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4182_, 1, v_a_4175_);
                    v___x_4181_ = v_reuseFailAlloc_4182_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4181_;
            }
            3 => {
                v_snd_4189_ = leanh::lean_ctor_get(v_val_4185_, 1);
                leanh::lean_inc(v_snd_4189_);
                leanh::lean_dec(v_val_4185_);
                if leanh::lean_obj_tag(v_snd_4189_) == 0 {
                    leanh::lean_del_object(v___x_4187_);
                    v_a_4190_ = leanh::lean_ctor_get(v___x_4173_, 1);
                    leanh::lean_inc(v_a_4190_);
                    leanh::lean_dec_ref_known(v___x_4173_, 2);
                    v_a_4191_ = leanh::lean_ctor_get(v_snd_4189_, 0);
                    v_isSharedCheck_4199_ = (!leanh::lean_is_exclusive(v_snd_4189_)) as u8;
                    if v_isSharedCheck_4199_ == 0 {
                        v___x_4193_ = v_snd_4189_;
                        v_isShared_4194_ = v_isSharedCheck_4199_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4191_);
                        leanh::lean_dec(v_snd_4189_);
                        v___x_4193_ = leanh::lean_box(0);
                        v_isShared_4194_ = v_isSharedCheck_4199_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_4200_ = leanh::lean_ctor_get(v___x_4173_, 1);
                    leanh::lean_inc(v_a_4200_);
                    leanh::lean_dec_ref_known(v___x_4173_, 2);
                    v_a_4201_ = leanh::lean_ctor_get(v_snd_4189_, 0);
                    v_isSharedCheck_4212_ = (!leanh::lean_is_exclusive(v_snd_4189_)) as u8;
                    if v_isSharedCheck_4212_ == 0 {
                        v___x_4203_ = v_snd_4189_;
                        v_isShared_4204_ = v_isSharedCheck_4212_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4201_);
                        leanh::lean_dec(v_snd_4189_);
                        v___x_4203_ = leanh::lean_box(0);
                        v_isShared_4204_ = v_isSharedCheck_4212_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4194_ == 0 {
                    v___x_4196_ = v___x_4193_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4198_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4198_, 0, v_a_4191_);
                    v___x_4196_ = v_reuseFailAlloc_4198_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4197_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg(v___x_4196_, v_a_4190_);
                leanh::lean_dec_ref(v___x_4196_);
                return v___x_4197_;
            }
            6 => {
                if v_isShared_4188_ == 0 {
                    leanh::lean_ctor_set(v___x_4187_, 0, v_a_4201_);
                    v___x_4206_ = v___x_4187_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4211_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_a_4201_);
                    v___x_4206_ = v_reuseFailAlloc_4211_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4204_ == 0 {
                    leanh::lean_ctor_set(v___x_4203_, 0, v___x_4206_);
                    v___x_4208_ = v___x_4203_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4210_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4210_, 0, v___x_4206_);
                    v___x_4208_ = v_reuseFailAlloc_4210_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4209_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg(v___x_4208_, v_a_4200_);
                leanh::lean_dec_ref(v___x_4208_);
                return v___x_4209_;
            }
            9 => {
                if v_isShared_4218_ == 0 {
                    v___x_4220_ = v___x_4217_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4221_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4221_, 0, v_a_4214_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4221_, 1, v_a_4215_);
                    v___x_4220_ = v_reuseFailAlloc_4221_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4220_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__0___boxed(
    mut v_env_4223_: *mut leanh::LeanObject,
    mut v_stx_4224_: *mut leanh::LeanObject,
    mut v___y_4225_: *mut leanh::LeanObject,
    mut v___y_4226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4227_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__0(v_env_4223_, v_stx_4224_, v___y_4225_, v___y_4226_);
    leanh::lean_dec_ref(v___y_4225_);
    return v_res_4227_;
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___redArg(
    mut v_as_4228_: *mut leanh::LeanObject,
    mut v___y_4229_: *mut leanh::LeanObject,
    mut v___y_4230_: *mut leanh::LeanObject,
    mut v___y_4231_: *mut leanh::LeanObject,
    mut v___y_4232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4237_: u8 = 0;
    let mut v_tail_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: u8 = 0;
    let mut v___x_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_4228_) == 0 {
                    v___x_4234_ = leanh::lean_box(0);
                    v___x_4235_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4235_, 0, v___x_4234_);
                    return v___x_4235_;
                } else {
                    v_options_4236_ = leanh::lean_ctor_get(v___y_4231_, 2);
                    v_hasTrace_4237_ = leanh::lean_ctor_get_uint8(
                        v_options_4236_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_4237_ == 0 {
                        v_tail_4238_ = leanh::lean_ctor_get(v_as_4228_, 1);
                        leanh::lean_inc(v_tail_4238_);
                        leanh::lean_dec_ref_known(v_as_4228_, 2);
                        v_as_4228_ = v_tail_4238_;
                        state = 0;
                        continue;
                    } else {
                        v_head_4240_ = leanh::lean_ctor_get(v_as_4228_, 0);
                        leanh::lean_inc(v_head_4240_);
                        v_tail_4241_ = leanh::lean_ctor_get(v_as_4228_, 1);
                        leanh::lean_inc(v_tail_4241_);
                        leanh::lean_dec_ref_known(v_as_4228_, 2);
                        v_fst_4242_ = leanh::lean_ctor_get(v_head_4240_, 0);
                        leanh::lean_inc_n(v_fst_4242_, 2);
                        v_snd_4243_ = leanh::lean_ctor_get(v_head_4240_, 1);
                        leanh::lean_inc(v_snd_4243_);
                        leanh::lean_dec(v_head_4240_);
                        v_inheritedTraceOptions_4244_ =
                            leanh::lean_ctor_get(v___y_4231_, 13);
                        v___x_4245_ = l_Lean_Elab_Tactic_Do_ProofMode_mRefineCore___closed__17;
                        v___x_4246_ = l_Lean_Name_append(v___x_4245_, v_fst_4242_);
                        v___x_4247_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_4244_,
                            v_options_4236_,
                            v___x_4246_,
                        );
                        leanh::lean_dec(v___x_4246_);
                        if v___x_4247_ == 0 {
                            leanh::lean_dec(v_snd_4243_);
                            leanh::lean_dec(v_fst_4242_);
                            v_as_4228_ = v_tail_4241_;
                            state = 0;
                            continue;
                        } else {
                            v___x_4249_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_4249_, 0, v_snd_4243_);
                            v___x_4250_ = l_Lean_MessageData_ofFormat(v___x_4249_);
                            v___x_4251_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__3___redArg(v_fst_4242_, v___x_4250_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_);
                            if leanh::lean_obj_tag(v___x_4251_) == 0 {
                                leanh::lean_dec_ref_known(v___x_4251_, 1);
                                v_as_4228_ = v_tail_4241_;
                                state = 0;
                                continue;
                            } else {
                                leanh::lean_dec(v_tail_4241_);
                                return v___x_4251_;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___redArg___boxed(
    mut v_as_4253_: *mut leanh::LeanObject,
    mut v___y_4254_: *mut leanh::LeanObject,
    mut v___y_4255_: *mut leanh::LeanObject,
    mut v___y_4256_: *mut leanh::LeanObject,
    mut v___y_4257_: *mut leanh::LeanObject,
    mut v___y_4258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4259_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___redArg(v_as_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_);
    leanh::lean_dec(v___y_4257_);
    leanh::lean_dec_ref(v___y_4256_);
    leanh::lean_dec(v___y_4255_);
    leanh::lean_dec_ref(v___y_4254_);
    return v_res_4259_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__1(
    mut v_env_4260_: *mut leanh::LeanObject,
    mut v_declName_4261_: *mut leanh::LeanObject,
    mut v___y_4262_: *mut leanh::LeanObject,
    mut v___y_4263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4264_: u8 = 0;
    let mut v_env_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: u8 = 0;
    let mut v___x_4268_: u8 = 0;
    v___x_4264_ = 0;
    v_env_4265_ = l_Lean_Environment_setExporting(v_env_4260_, v___x_4264_);
    leanh::lean_inc(v_declName_4261_);
    v___x_4266_ = l_Lean_mkPrivateName(v_env_4265_, v_declName_4261_);
    v___x_4267_ = 1;
    leanh::lean_inc_ref(v_env_4265_);
    v___x_4268_ = l_Lean_Environment_contains(v_env_4265_, v___x_4266_, v___x_4267_);
    if v___x_4268_ == 0 {
        let mut v___x_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4270_: u8 = 0;
        let mut v___x_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4269_ = l_Lean_privateToUserName(v_declName_4261_);
        v___x_4270_ = l_Lean_Environment_contains(v_env_4265_, v___x_4269_, v___x_4267_);
        v___x_4271_ = leanh::lean_box((v___x_4270_) as usize);
        v___x_4272_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4272_, 0, v___x_4271_);
        leanh::lean_ctor_set(v___x_4272_, 1, v___y_4263_);
        return v___x_4272_;
    } else {
        let mut v___x_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_env_4265_);
        leanh::lean_dec(v_declName_4261_);
        v___x_4273_ = leanh::lean_box((v___x_4268_) as usize);
        v___x_4274_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4274_, 0, v___x_4273_);
        leanh::lean_ctor_set(v___x_4274_, 1, v___y_4263_);
        return v___x_4274_;
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__1___boxed(
    mut v_env_4275_: *mut leanh::LeanObject,
    mut v_declName_4276_: *mut leanh::LeanObject,
    mut v___y_4277_: *mut leanh::LeanObject,
    mut v___y_4278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4279_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__1(v_env_4275_, v_declName_4276_, v___y_4277_, v___y_4278_);
    leanh::lean_dec_ref(v___y_4277_);
    return v_res_4279_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__2(
    mut v_env_4280_: *mut leanh::LeanObject,
    mut v_currNamespace_4281_: *mut leanh::LeanObject,
    mut v_openDecls_4282_: *mut leanh::LeanObject,
    mut v_n_4283_: *mut leanh::LeanObject,
    mut v___y_4284_: *mut leanh::LeanObject,
    mut v___y_4285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4286_ = l_Lean_ResolveName_resolveNamespace(
        v_env_4280_,
        v_currNamespace_4281_,
        v_openDecls_4282_,
        v_n_4283_,
    );
    v___x_4287_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4287_, 0, v___x_4286_);
    leanh::lean_ctor_set(v___x_4287_, 1, v___y_4285_);
    return v___x_4287_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__2___boxed(
    mut v_env_4288_: *mut leanh::LeanObject,
    mut v_currNamespace_4289_: *mut leanh::LeanObject,
    mut v_openDecls_4290_: *mut leanh::LeanObject,
    mut v_n_4291_: *mut leanh::LeanObject,
    mut v___y_4292_: *mut leanh::LeanObject,
    mut v___y_4293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4294_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__2(v_env_4288_, v_currNamespace_4289_, v_openDecls_4290_, v_n_4291_, v___y_4292_, v___y_4293_);
    leanh::lean_dec_ref(v___y_4292_);
    return v_res_4294_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg(
    mut v_x_4296_: *mut leanh::LeanObject,
    mut v___y_4297_: *mut leanh::LeanObject,
    mut v___y_4298_: *mut leanh::LeanObject,
    mut v___y_4299_: *mut leanh::LeanObject,
    mut v___y_4300_: *mut leanh::LeanObject,
    mut v___y_4301_: *mut leanh::LeanObject,
    mut v___y_4302_: *mut leanh::LeanObject,
    mut v___y_4303_: *mut leanh::LeanObject,
    mut v___y_4304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_methods_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroScope_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4346_: u8 = 0;
    let mut v___x_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4354_: u8 = 0;
    let mut v___x_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4358_: u8 = 0;
    let mut v_unused_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4363_: u8 = 0;
    let mut v___x_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4367_: u8 = 0;
    let mut v_reuseFailAlloc_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4369_: u8 = 0;
    let mut v_unused_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4374_: u8 = 0;
    let mut v___x_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4378_: u8 = 0;
    let mut v_a_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: u8 = 0;
    let mut v___x_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4306_ = lean_st_ref_get(v___y_4304_);
                v_env_4307_ = leanh::lean_ctor_get(v___x_4306_, 0);
                leanh::lean_inc_ref_n(v_env_4307_, 4);
                leanh::lean_dec(v___x_4306_);
                v_options_4308_ = leanh::lean_ctor_get(v___y_4303_, 2);
                v_currRecDepth_4309_ = leanh::lean_ctor_get(v___y_4303_, 3);
                v_maxRecDepth_4310_ = leanh::lean_ctor_get(v___y_4303_, 4);
                v_ref_4311_ = leanh::lean_ctor_get(v___y_4303_, 5);
                v_currNamespace_4312_ = leanh::lean_ctor_get(v___y_4303_, 6);
                v_openDecls_4313_ = leanh::lean_ctor_get(v___y_4303_, 7);
                v_quotContext_4314_ = leanh::lean_ctor_get(v___y_4303_, 10);
                v_currMacroScope_4315_ = leanh::lean_ctor_get(v___y_4303_, 11);
                v___x_4316_ = lean_st_ref_get(v___y_4304_);
                v_nextMacroScope_4317_ = leanh::lean_ctor_get(v___x_4316_, 1);
                leanh::lean_inc(v_nextMacroScope_4317_);
                leanh::lean_dec(v___x_4316_);
                v___f_4318_ = leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 4, 1);
                leanh::lean_closure_set(v___f_4318_, 0, v_env_4307_);
                v___f_4319_ = leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 1);
                leanh::lean_closure_set(v___f_4319_, 0, v_env_4307_);
                leanh::lean_inc_n(v_openDecls_4313_, 2);
                leanh::lean_inc_n(v_currNamespace_4312_, 3);
                v___f_4320_ = leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__2___boxed as *mut core::ffi::c_void, 6, 3);
                leanh::lean_closure_set(v___f_4320_, 0, v_env_4307_);
                leanh::lean_closure_set(v___f_4320_, 1, v_currNamespace_4312_);
                leanh::lean_closure_set(v___f_4320_, 2, v_openDecls_4313_);
                v___f_4321_ = leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__3___boxed as *mut core::ffi::c_void, 3, 1);
                leanh::lean_closure_set(v___f_4321_, 0, v_currNamespace_4312_);
                leanh::lean_inc_ref(v_options_4308_);
                v___f_4322_ = leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___lam__4___boxed as *mut core::ffi::c_void, 7, 4);
                leanh::lean_closure_set(v___f_4322_, 0, v_env_4307_);
                leanh::lean_closure_set(v___f_4322_, 1, v_options_4308_);
                leanh::lean_closure_set(v___f_4322_, 2, v_currNamespace_4312_);
                leanh::lean_closure_set(v___f_4322_, 3, v_openDecls_4313_);
                v_methods_4323_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v_methods_4323_, 0, v___f_4318_);
                leanh::lean_ctor_set(v_methods_4323_, 1, v___f_4321_);
                leanh::lean_ctor_set(v_methods_4323_, 2, v___f_4319_);
                leanh::lean_ctor_set(v_methods_4323_, 3, v___f_4320_);
                leanh::lean_ctor_set(v_methods_4323_, 4, v___f_4322_);
                leanh::lean_inc(v_ref_4311_);
                leanh::lean_inc(v_maxRecDepth_4310_);
                leanh::lean_inc(v_currRecDepth_4309_);
                leanh::lean_inc(v_currMacroScope_4315_);
                leanh::lean_inc(v_quotContext_4314_);
                v___x_4324_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                leanh::lean_ctor_set(v___x_4324_, 0, v_methods_4323_);
                leanh::lean_ctor_set(v___x_4324_, 1, v_quotContext_4314_);
                leanh::lean_ctor_set(v___x_4324_, 2, v_currMacroScope_4315_);
                leanh::lean_ctor_set(v___x_4324_, 3, v_currRecDepth_4309_);
                leanh::lean_ctor_set(v___x_4324_, 4, v_maxRecDepth_4310_);
                leanh::lean_ctor_set(v___x_4324_, 5, v_ref_4311_);
                v___x_4325_ = leanh::lean_box(0);
                v___x_4326_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4326_, 0, v_nextMacroScope_4317_);
                leanh::lean_ctor_set(v___x_4326_, 1, v___x_4325_);
                leanh::lean_ctor_set(v___x_4326_, 2, v___x_4325_);
                v___x_4327_ = leanh::lean_apply_2(v_x_4296_, v___x_4324_, v___x_4326_);
                if leanh::lean_obj_tag(v___x_4327_) == 0 {
                    v_a_4328_ = leanh::lean_ctor_get(v___x_4327_, 1);
                    leanh::lean_inc(v_a_4328_);
                    v_a_4329_ = leanh::lean_ctor_get(v___x_4327_, 0);
                    leanh::lean_inc(v_a_4329_);
                    leanh::lean_dec_ref_known(v___x_4327_, 2);
                    v_macroScope_4330_ = leanh::lean_ctor_get(v_a_4328_, 0);
                    leanh::lean_inc(v_macroScope_4330_);
                    v_traceMsgs_4331_ = leanh::lean_ctor_get(v_a_4328_, 1);
                    leanh::lean_inc(v_traceMsgs_4331_);
                    v_expandedMacroDecls_4332_ = leanh::lean_ctor_get(v_a_4328_, 2);
                    leanh::lean_inc(v_expandedMacroDecls_4332_);
                    leanh::lean_dec(v_a_4328_);
                    v___x_4333_ = leanh::lean_box(0);
                    v___x_4334_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___redArg(v_expandedMacroDecls_4332_, v___x_4333_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
                    leanh::lean_dec(v_expandedMacroDecls_4332_);
                    if leanh::lean_obj_tag(v___x_4334_) == 0 {
                        leanh::lean_dec_ref_known(v___x_4334_, 1);
                        v___x_4335_ = lean_st_ref_take(v___y_4304_);
                        v_env_4336_ = leanh::lean_ctor_get(v___x_4335_, 0);
                        v_ngen_4337_ = leanh::lean_ctor_get(v___x_4335_, 2);
                        v_auxDeclNGen_4338_ = leanh::lean_ctor_get(v___x_4335_, 3);
                        v_traceState_4339_ = leanh::lean_ctor_get(v___x_4335_, 4);
                        v_cache_4340_ = leanh::lean_ctor_get(v___x_4335_, 5);
                        v_messages_4341_ = leanh::lean_ctor_get(v___x_4335_, 6);
                        v_infoState_4342_ = leanh::lean_ctor_get(v___x_4335_, 7);
                        v_snapshotTasks_4343_ = leanh::lean_ctor_get(v___x_4335_, 8);
                        v_isSharedCheck_4369_ =
                            (!leanh::lean_is_exclusive(v___x_4335_)) as u8;
                        if v_isSharedCheck_4369_ == 0 {
                            v_unused_4370_ = leanh::lean_ctor_get(v___x_4335_, 1);
                            leanh::lean_dec(v_unused_4370_);
                            v___x_4345_ = v___x_4335_;
                            v_isShared_4346_ = v_isSharedCheck_4369_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_snapshotTasks_4343_);
                            leanh::lean_inc(v_infoState_4342_);
                            leanh::lean_inc(v_messages_4341_);
                            leanh::lean_inc(v_cache_4340_);
                            leanh::lean_inc(v_traceState_4339_);
                            leanh::lean_inc(v_auxDeclNGen_4338_);
                            leanh::lean_inc(v_ngen_4337_);
                            leanh::lean_inc(v_env_4336_);
                            leanh::lean_dec(v___x_4335_);
                            v___x_4345_ = leanh::lean_box(0);
                            v_isShared_4346_ = v_isSharedCheck_4369_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_traceMsgs_4331_);
                        leanh::lean_dec(v_macroScope_4330_);
                        leanh::lean_dec(v_a_4329_);
                        v_a_4371_ = leanh::lean_ctor_get(v___x_4334_, 0);
                        v_isSharedCheck_4378_ =
                            (!leanh::lean_is_exclusive(v___x_4334_)) as u8;
                        if v_isSharedCheck_4378_ == 0 {
                            v___x_4373_ = v___x_4334_;
                            v_isShared_4374_ = v_isSharedCheck_4378_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4371_);
                            leanh::lean_dec(v___x_4334_);
                            v___x_4373_ = leanh::lean_box(0);
                            v_isShared_4374_ = v_isSharedCheck_4378_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    v_a_4379_ = leanh::lean_ctor_get(v___x_4327_, 0);
                    leanh::lean_inc(v_a_4379_);
                    leanh::lean_dec_ref_known(v___x_4327_, 2);
                    if leanh::lean_obj_tag(v_a_4379_) == 0 {
                        v_a_4380_ = leanh::lean_ctor_get(v_a_4379_, 0);
                        leanh::lean_inc(v_a_4380_);
                        v_a_4381_ = leanh::lean_ctor_get(v_a_4379_, 1);
                        leanh::lean_inc_ref(v_a_4381_);
                        leanh::lean_dec_ref_known(v_a_4379_, 2);
                        v___x_4382_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___closed__0;
                        v___x_4383_ = lean_string_dec_eq(v_a_4381_, v___x_4382_);
                        if v___x_4383_ == 0 {
                            v___x_4384_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_4384_, 0, v_a_4381_);
                            v___x_4385_ = l_Lean_MessageData_ofFormat(v___x_4384_);
                            v___x_4386_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___redArg(v_a_4380_, v___x_4385_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
                            leanh::lean_dec(v_a_4380_);
                            return v___x_4386_;
                        } else {
                            leanh::lean_dec_ref(v_a_4381_);
                            v___x_4387_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg(v_a_4380_);
                            return v___x_4387_;
                        }
                    } else {
                        v___x_4388_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg();
                        return v___x_4388_;
                    }
                }
            }
            1 => {
                if v_isShared_4346_ == 0 {
                    leanh::lean_ctor_set(v___x_4345_, 1, v_macroScope_4330_);
                    v___x_4348_ = v___x_4345_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4368_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4368_, 0, v_env_4336_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4368_, 1, v_macroScope_4330_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4368_, 2, v_ngen_4337_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4368_, 3, v_auxDeclNGen_4338_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4368_, 4, v_traceState_4339_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4368_, 5, v_cache_4340_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4368_, 6, v_messages_4341_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4368_, 7, v_infoState_4342_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4368_, 8, v_snapshotTasks_4343_);
                    v___x_4348_ = v_reuseFailAlloc_4368_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4349_ = lean_st_ref_set(v___y_4304_, v___x_4348_);
                v___x_4350_ = l_List_reverse___redArg(v_traceMsgs_4331_);
                v___x_4351_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___redArg(v___x_4350_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
                if leanh::lean_obj_tag(v___x_4351_) == 0 {
                    v_isSharedCheck_4358_ = (!leanh::lean_is_exclusive(v___x_4351_)) as u8;
                    if v_isSharedCheck_4358_ == 0 {
                        v_unused_4359_ = leanh::lean_ctor_get(v___x_4351_, 0);
                        leanh::lean_dec(v_unused_4359_);
                        v___x_4353_ = v___x_4351_;
                        v_isShared_4354_ = v_isSharedCheck_4358_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_4351_);
                        v___x_4353_ = leanh::lean_box(0);
                        v_isShared_4354_ = v_isSharedCheck_4358_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4329_);
                    v_a_4360_ = leanh::lean_ctor_get(v___x_4351_, 0);
                    v_isSharedCheck_4367_ = (!leanh::lean_is_exclusive(v___x_4351_)) as u8;
                    if v_isSharedCheck_4367_ == 0 {
                        v___x_4362_ = v___x_4351_;
                        v_isShared_4363_ = v_isSharedCheck_4367_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4360_);
                        leanh::lean_dec(v___x_4351_);
                        v___x_4362_ = leanh::lean_box(0);
                        v_isShared_4363_ = v_isSharedCheck_4367_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4354_ == 0 {
                    leanh::lean_ctor_set(v___x_4353_, 0, v_a_4329_);
                    v___x_4356_ = v___x_4353_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4357_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4357_, 0, v_a_4329_);
                    v___x_4356_ = v_reuseFailAlloc_4357_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4356_;
            }
            5 => {
                if v_isShared_4363_ == 0 {
                    v___x_4365_ = v___x_4362_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4366_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4366_, 0, v_a_4360_);
                    v___x_4365_ = v_reuseFailAlloc_4366_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4365_;
            }
            7 => {
                if v_isShared_4374_ == 0 {
                    v___x_4376_ = v___x_4373_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4377_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4377_, 0, v_a_4371_);
                    v___x_4376_ = v_reuseFailAlloc_4377_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4376_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg___boxed(
    mut v_x_4389_: *mut leanh::LeanObject,
    mut v___y_4390_: *mut leanh::LeanObject,
    mut v___y_4391_: *mut leanh::LeanObject,
    mut v___y_4392_: *mut leanh::LeanObject,
    mut v___y_4393_: *mut leanh::LeanObject,
    mut v___y_4394_: *mut leanh::LeanObject,
    mut v___y_4395_: *mut leanh::LeanObject,
    mut v___y_4396_: *mut leanh::LeanObject,
    mut v___y_4397_: *mut leanh::LeanObject,
    mut v___y_4398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4399_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg(
            v_x_4389_,
            v___y_4390_,
            v___y_4391_,
            v___y_4392_,
            v___y_4393_,
            v___y_4394_,
            v___y_4395_,
            v___y_4396_,
            v___y_4397_,
        );
    leanh::lean_dec(v___y_4397_);
    leanh::lean_dec_ref(v___y_4396_);
    leanh::lean_dec(v___y_4395_);
    leanh::lean_dec_ref(v___y_4394_);
    leanh::lean_dec(v___y_4393_);
    leanh::lean_dec_ref(v___y_4392_);
    leanh::lean_dec(v___y_4391_);
    leanh::lean_dec_ref(v___y_4390_);
    return v_res_4399_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine(
    mut v_x_4410_: *mut leanh::LeanObject,
    mut v_a_4411_: *mut leanh::LeanObject,
    mut v_a_4412_: *mut leanh::LeanObject,
    mut v_a_4413_: *mut leanh::LeanObject,
    mut v_a_4414_: *mut leanh::LeanObject,
    mut v_a_4415_: *mut leanh::LeanObject,
    mut v_a_4416_: *mut leanh::LeanObject,
    mut v_a_4417_: *mut leanh::LeanObject,
    mut v_a_4418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: u8 = 0;
    let mut v___x_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pat_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4438_: u8 = 0;
    let mut v___x_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4442_: u8 = 0;
    let mut v_a_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4446_: u8 = 0;
    let mut v___x_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4450_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4420_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3;
                leanh::lean_inc(v_x_4410_);
                v___x_4421_ = l_Lean_Syntax_isOfKind(v_x_4410_, v___x_4420_);
                if v___x_4421_ == 0 {
                    leanh::lean_dec(v_x_4410_);
                    v___x_4422_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg();
                    return v___x_4422_;
                } else {
                    v___x_4423_ = leanh::lean_unsigned_to_nat(1);
                    v_pat_4424_ = l_Lean_Syntax_getArg(v_x_4410_, v___x_4423_);
                    leanh::lean_dec(v_x_4410_);
                    v___x_4425_ = leanh::lean_alloc_closure(
                        l_Lean_Parser_Tactic_MRefinePat_parse___boxed as *mut core::ffi::c_void,
                        3,
                        1,
                    );
                    leanh::lean_closure_set(v___x_4425_, 0, v_pat_4424_);
                    v___x_4426_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg(v___x_4425_, v_a_4411_, v_a_4412_, v_a_4413_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_);
                    if leanh::lean_obj_tag(v___x_4426_) == 0 {
                        v_a_4427_ = leanh::lean_ctor_get(v___x_4426_, 0);
                        leanh::lean_inc(v_a_4427_);
                        leanh::lean_dec_ref_known(v___x_4426_, 1);
                        v___x_4428_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(
                            v_a_4412_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_,
                        );
                        if leanh::lean_obj_tag(v___x_4428_) == 0 {
                            v_a_4429_ = leanh::lean_ctor_get(v___x_4428_, 0);
                            leanh::lean_inc(v_a_4429_);
                            leanh::lean_dec_ref_known(v___x_4428_, 1);
                            v_fst_4430_ = leanh::lean_ctor_get(v_a_4429_, 0);
                            leanh::lean_inc_n(v_fst_4430_, 2);
                            v_snd_4431_ = leanh::lean_ctor_get(v_a_4429_, 1);
                            leanh::lean_inc(v_snd_4431_);
                            leanh::lean_dec(v_a_4429_);
                            v___x_4432_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__4;
                            v___f_4433_ = leanh::lean_alloc_closure(
                                l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___lam__1___boxed
                                    as *mut core::ffi::c_void,
                                13,
                                4,
                            );
                            leanh::lean_closure_set(v___f_4433_, 0, v___x_4432_);
                            leanh::lean_closure_set(v___f_4433_, 1, v_snd_4431_);
                            leanh::lean_closure_set(v___f_4433_, 2, v_a_4427_);
                            leanh::lean_closure_set(v___f_4433_, 3, v_fst_4430_);
                            v___x_4434_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__2___redArg(v_fst_4430_, v___f_4433_, v_a_4411_, v_a_4412_, v_a_4413_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_);
                            return v___x_4434_;
                        } else {
                            leanh::lean_dec(v_a_4427_);
                            v_a_4435_ = leanh::lean_ctor_get(v___x_4428_, 0);
                            v_isSharedCheck_4442_ =
                                (!leanh::lean_is_exclusive(v___x_4428_)) as u8;
                            if v_isSharedCheck_4442_ == 0 {
                                v___x_4437_ = v___x_4428_;
                                v_isShared_4438_ = v_isSharedCheck_4442_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4435_);
                                leanh::lean_dec(v___x_4428_);
                                v___x_4437_ = leanh::lean_box(0);
                                v_isShared_4438_ = v_isSharedCheck_4442_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v_a_4443_ = leanh::lean_ctor_get(v___x_4426_, 0);
                        v_isSharedCheck_4450_ =
                            (!leanh::lean_is_exclusive(v___x_4426_)) as u8;
                        if v_isSharedCheck_4450_ == 0 {
                            v___x_4445_ = v___x_4426_;
                            v_isShared_4446_ = v_isSharedCheck_4450_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4443_);
                            leanh::lean_dec(v___x_4426_);
                            v___x_4445_ = leanh::lean_box(0);
                            v_isShared_4446_ = v_isSharedCheck_4450_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4438_ == 0 {
                    v___x_4440_ = v___x_4437_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4441_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4441_, 0, v_a_4435_);
                    v___x_4440_ = v_reuseFailAlloc_4441_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4440_;
            }
            3 => {
                if v_isShared_4446_ == 0 {
                    v___x_4448_ = v___x_4445_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4449_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4449_, 0, v_a_4443_);
                    v___x_4448_ = v_reuseFailAlloc_4449_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4448_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___boxed(
    mut v_x_4451_: *mut leanh::LeanObject,
    mut v_a_4452_: *mut leanh::LeanObject,
    mut v_a_4453_: *mut leanh::LeanObject,
    mut v_a_4454_: *mut leanh::LeanObject,
    mut v_a_4455_: *mut leanh::LeanObject,
    mut v_a_4456_: *mut leanh::LeanObject,
    mut v_a_4457_: *mut leanh::LeanObject,
    mut v_a_4458_: *mut leanh::LeanObject,
    mut v_a_4459_: *mut leanh::LeanObject,
    mut v_a_4460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4461_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine(
        v_x_4451_, v_a_4452_, v_a_4453_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_,
        v_a_4459_,
    );
    leanh::lean_dec(v_a_4459_);
    leanh::lean_dec_ref(v_a_4458_);
    leanh::lean_dec(v_a_4457_);
    leanh::lean_dec_ref(v_a_4456_);
    leanh::lean_dec(v_a_4455_);
    leanh::lean_dec_ref(v_a_4454_);
    leanh::lean_dec(v_a_4453_);
    leanh::lean_dec_ref(v_a_4452_);
    return v_res_4461_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0(
    mut v_00_u03b1_4462_: *mut leanh::LeanObject,
    mut v_x_4463_: *mut leanh::LeanObject,
    mut v___y_4464_: *mut leanh::LeanObject,
    mut v___y_4465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4466_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___redArg(v_x_4463_, v___y_4465_);
    return v___x_4466_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0___boxed(
    mut v_00_u03b1_4467_: *mut leanh::LeanObject,
    mut v_x_4468_: *mut leanh::LeanObject,
    mut v___y_4469_: *mut leanh::LeanObject,
    mut v___y_4470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4471_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__0(v_00_u03b1_4467_, v_x_4468_, v___y_4469_, v___y_4470_);
    leanh::lean_dec_ref(v___y_4469_);
    leanh::lean_dec_ref(v_x_4468_);
    return v_res_4471_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5(
    mut v_00_u03b1_4472_: *mut leanh::LeanObject,
    mut v_ref_4473_: *mut leanh::LeanObject,
    mut v___y_4474_: *mut leanh::LeanObject,
    mut v___y_4475_: *mut leanh::LeanObject,
    mut v___y_4476_: *mut leanh::LeanObject,
    mut v___y_4477_: *mut leanh::LeanObject,
    mut v___y_4478_: *mut leanh::LeanObject,
    mut v___y_4479_: *mut leanh::LeanObject,
    mut v___y_4480_: *mut leanh::LeanObject,
    mut v___y_4481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4483_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___redArg(v_ref_4473_);
    return v___x_4483_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5___boxed(
    mut v_00_u03b1_4484_: *mut leanh::LeanObject,
    mut v_ref_4485_: *mut leanh::LeanObject,
    mut v___y_4486_: *mut leanh::LeanObject,
    mut v___y_4487_: *mut leanh::LeanObject,
    mut v___y_4488_: *mut leanh::LeanObject,
    mut v___y_4489_: *mut leanh::LeanObject,
    mut v___y_4490_: *mut leanh::LeanObject,
    mut v___y_4491_: *mut leanh::LeanObject,
    mut v___y_4492_: *mut leanh::LeanObject,
    mut v___y_4493_: *mut leanh::LeanObject,
    mut v___y_4494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4495_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__5(v_00_u03b1_4484_, v_ref_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_);
    leanh::lean_dec(v___y_4493_);
    leanh::lean_dec_ref(v___y_4492_);
    leanh::lean_dec(v___y_4491_);
    leanh::lean_dec_ref(v___y_4490_);
    leanh::lean_dec(v___y_4489_);
    leanh::lean_dec_ref(v___y_4488_);
    leanh::lean_dec(v___y_4487_);
    leanh::lean_dec_ref(v___y_4486_);
    return v_res_4495_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0(
    mut v_00_u03b1_4496_: *mut leanh::LeanObject,
    mut v_x_4497_: *mut leanh::LeanObject,
    mut v___y_4498_: *mut leanh::LeanObject,
    mut v___y_4499_: *mut leanh::LeanObject,
    mut v___y_4500_: *mut leanh::LeanObject,
    mut v___y_4501_: *mut leanh::LeanObject,
    mut v___y_4502_: *mut leanh::LeanObject,
    mut v___y_4503_: *mut leanh::LeanObject,
    mut v___y_4504_: *mut leanh::LeanObject,
    mut v___y_4505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4507_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___redArg(
            v_x_4497_,
            v___y_4498_,
            v___y_4499_,
            v___y_4500_,
            v___y_4501_,
            v___y_4502_,
            v___y_4503_,
            v___y_4504_,
            v___y_4505_,
        );
    return v___x_4507_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0___boxed(
    mut v_00_u03b1_4508_: *mut leanh::LeanObject,
    mut v_x_4509_: *mut leanh::LeanObject,
    mut v___y_4510_: *mut leanh::LeanObject,
    mut v___y_4511_: *mut leanh::LeanObject,
    mut v___y_4512_: *mut leanh::LeanObject,
    mut v___y_4513_: *mut leanh::LeanObject,
    mut v___y_4514_: *mut leanh::LeanObject,
    mut v___y_4515_: *mut leanh::LeanObject,
    mut v___y_4516_: *mut leanh::LeanObject,
    mut v___y_4517_: *mut leanh::LeanObject,
    mut v___y_4518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4519_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0(
        v_00_u03b1_4508_,
        v_x_4509_,
        v___y_4510_,
        v___y_4511_,
        v___y_4512_,
        v___y_4513_,
        v___y_4514_,
        v___y_4515_,
        v___y_4516_,
        v___y_4517_,
    );
    leanh::lean_dec(v___y_4517_);
    leanh::lean_dec_ref(v___y_4516_);
    leanh::lean_dec(v___y_4515_);
    leanh::lean_dec_ref(v___y_4514_);
    leanh::lean_dec(v___y_4513_);
    leanh::lean_dec_ref(v___y_4512_);
    leanh::lean_dec(v___y_4511_);
    leanh::lean_dec_ref(v___y_4510_);
    return v_res_4519_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1(
    mut v_mvarId_4520_: *mut leanh::LeanObject,
    mut v_val_4521_: *mut leanh::LeanObject,
    mut v___y_4522_: *mut leanh::LeanObject,
    mut v___y_4523_: *mut leanh::LeanObject,
    mut v___y_4524_: *mut leanh::LeanObject,
    mut v___y_4525_: *mut leanh::LeanObject,
    mut v___y_4526_: *mut leanh::LeanObject,
    mut v___y_4527_: *mut leanh::LeanObject,
    mut v___y_4528_: *mut leanh::LeanObject,
    mut v___y_4529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4531_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___redArg(
            v_mvarId_4520_,
            v_val_4521_,
            v___y_4527_,
        );
    return v___x_4531_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1___boxed(
    mut v_mvarId_4532_: *mut leanh::LeanObject,
    mut v_val_4533_: *mut leanh::LeanObject,
    mut v___y_4534_: *mut leanh::LeanObject,
    mut v___y_4535_: *mut leanh::LeanObject,
    mut v___y_4536_: *mut leanh::LeanObject,
    mut v___y_4537_: *mut leanh::LeanObject,
    mut v___y_4538_: *mut leanh::LeanObject,
    mut v___y_4539_: *mut leanh::LeanObject,
    mut v___y_4540_: *mut leanh::LeanObject,
    mut v___y_4541_: *mut leanh::LeanObject,
    mut v___y_4542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4543_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1(
        v_mvarId_4532_,
        v_val_4533_,
        v___y_4534_,
        v___y_4535_,
        v___y_4536_,
        v___y_4537_,
        v___y_4538_,
        v___y_4539_,
        v___y_4540_,
        v___y_4541_,
    );
    leanh::lean_dec(v___y_4541_);
    leanh::lean_dec_ref(v___y_4540_);
    leanh::lean_dec(v___y_4539_);
    leanh::lean_dec_ref(v___y_4538_);
    leanh::lean_dec(v___y_4537_);
    leanh::lean_dec_ref(v___y_4536_);
    leanh::lean_dec(v___y_4535_);
    leanh::lean_dec_ref(v___y_4534_);
    return v_res_4543_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2(
    mut v_as_4544_: *mut leanh::LeanObject,
    mut v_as_x27_4545_: *mut leanh::LeanObject,
    mut v_b_4546_: *mut leanh::LeanObject,
    mut v_a_4547_: *mut leanh::LeanObject,
    mut v___y_4548_: *mut leanh::LeanObject,
    mut v___y_4549_: *mut leanh::LeanObject,
    mut v___y_4550_: *mut leanh::LeanObject,
    mut v___y_4551_: *mut leanh::LeanObject,
    mut v___y_4552_: *mut leanh::LeanObject,
    mut v___y_4553_: *mut leanh::LeanObject,
    mut v___y_4554_: *mut leanh::LeanObject,
    mut v___y_4555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4557_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___redArg(v_as_x27_4545_, v_b_4546_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_);
    return v___x_4557_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2___boxed(
    mut v_as_4558_: *mut leanh::LeanObject,
    mut v_as_x27_4559_: *mut leanh::LeanObject,
    mut v_b_4560_: *mut leanh::LeanObject,
    mut v_a_4561_: *mut leanh::LeanObject,
    mut v___y_4562_: *mut leanh::LeanObject,
    mut v___y_4563_: *mut leanh::LeanObject,
    mut v___y_4564_: *mut leanh::LeanObject,
    mut v___y_4565_: *mut leanh::LeanObject,
    mut v___y_4566_: *mut leanh::LeanObject,
    mut v___y_4567_: *mut leanh::LeanObject,
    mut v___y_4568_: *mut leanh::LeanObject,
    mut v___y_4569_: *mut leanh::LeanObject,
    mut v___y_4570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4571_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__2(v_as_4558_, v_as_x27_4559_, v_b_4560_, v_a_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_);
    leanh::lean_dec(v___y_4569_);
    leanh::lean_dec_ref(v___y_4568_);
    leanh::lean_dec(v___y_4567_);
    leanh::lean_dec_ref(v___y_4566_);
    leanh::lean_dec(v___y_4565_);
    leanh::lean_dec_ref(v___y_4564_);
    leanh::lean_dec(v___y_4563_);
    leanh::lean_dec_ref(v___y_4562_);
    leanh::lean_dec(v_as_x27_4559_);
    leanh::lean_dec(v_as_4558_);
    return v_res_4571_;
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3(
    mut v_as_4572_: *mut leanh::LeanObject,
    mut v___y_4573_: *mut leanh::LeanObject,
    mut v___y_4574_: *mut leanh::LeanObject,
    mut v___y_4575_: *mut leanh::LeanObject,
    mut v___y_4576_: *mut leanh::LeanObject,
    mut v___y_4577_: *mut leanh::LeanObject,
    mut v___y_4578_: *mut leanh::LeanObject,
    mut v___y_4579_: *mut leanh::LeanObject,
    mut v___y_4580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4582_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___redArg(v_as_4572_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
    return v___x_4582_;
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3___boxed(
    mut v_as_4583_: *mut leanh::LeanObject,
    mut v___y_4584_: *mut leanh::LeanObject,
    mut v___y_4585_: *mut leanh::LeanObject,
    mut v___y_4586_: *mut leanh::LeanObject,
    mut v___y_4587_: *mut leanh::LeanObject,
    mut v___y_4588_: *mut leanh::LeanObject,
    mut v___y_4589_: *mut leanh::LeanObject,
    mut v___y_4590_: *mut leanh::LeanObject,
    mut v___y_4591_: *mut leanh::LeanObject,
    mut v___y_4592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4593_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__3(v_as_4583_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_);
    leanh::lean_dec(v___y_4591_);
    leanh::lean_dec_ref(v___y_4590_);
    leanh::lean_dec(v___y_4589_);
    leanh::lean_dec_ref(v___y_4588_);
    leanh::lean_dec(v___y_4587_);
    leanh::lean_dec_ref(v___y_4586_);
    leanh::lean_dec(v___y_4585_);
    leanh::lean_dec_ref(v___y_4584_);
    return v_res_4593_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4(
    mut v_00_u03b1_4594_: *mut leanh::LeanObject,
    mut v_ref_4595_: *mut leanh::LeanObject,
    mut v_msg_4596_: *mut leanh::LeanObject,
    mut v___y_4597_: *mut leanh::LeanObject,
    mut v___y_4598_: *mut leanh::LeanObject,
    mut v___y_4599_: *mut leanh::LeanObject,
    mut v___y_4600_: *mut leanh::LeanObject,
    mut v___y_4601_: *mut leanh::LeanObject,
    mut v___y_4602_: *mut leanh::LeanObject,
    mut v___y_4603_: *mut leanh::LeanObject,
    mut v___y_4604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4606_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___redArg(v_ref_4595_, v_msg_4596_, v___y_4601_, v___y_4602_, v___y_4603_, v___y_4604_);
    return v___x_4606_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4___boxed(
    mut v_00_u03b1_4607_: *mut leanh::LeanObject,
    mut v_ref_4608_: *mut leanh::LeanObject,
    mut v_msg_4609_: *mut leanh::LeanObject,
    mut v___y_4610_: *mut leanh::LeanObject,
    mut v___y_4611_: *mut leanh::LeanObject,
    mut v___y_4612_: *mut leanh::LeanObject,
    mut v___y_4613_: *mut leanh::LeanObject,
    mut v___y_4614_: *mut leanh::LeanObject,
    mut v___y_4615_: *mut leanh::LeanObject,
    mut v___y_4616_: *mut leanh::LeanObject,
    mut v___y_4617_: *mut leanh::LeanObject,
    mut v___y_4618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4619_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__4(v_00_u03b1_4607_, v_ref_4608_, v_msg_4609_, v___y_4610_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_);
    leanh::lean_dec(v___y_4617_);
    leanh::lean_dec_ref(v___y_4616_);
    leanh::lean_dec(v___y_4615_);
    leanh::lean_dec_ref(v___y_4614_);
    leanh::lean_dec(v___y_4613_);
    leanh::lean_dec_ref(v___y_4612_);
    leanh::lean_dec(v___y_4611_);
    leanh::lean_dec_ref(v___y_4610_);
    leanh::lean_dec(v_ref_4608_);
    return v_res_4619_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7(
    mut v_00_u03b2_4620_: *mut leanh::LeanObject,
    mut v_x_4621_: *mut leanh::LeanObject,
    mut v_x_4622_: *mut leanh::LeanObject,
    mut v_x_4623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4624_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7___redArg(v_x_4621_, v_x_4622_, v_x_4623_);
    return v___x_4624_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3(
    mut v_mod_4625_: *mut leanh::LeanObject,
    mut v_isMeta_4626_: u8,
    mut v_hint_4627_: *mut leanh::LeanObject,
    mut v___y_4628_: *mut leanh::LeanObject,
    mut v___y_4629_: *mut leanh::LeanObject,
    mut v___y_4630_: *mut leanh::LeanObject,
    mut v___y_4631_: *mut leanh::LeanObject,
    mut v___y_4632_: *mut leanh::LeanObject,
    mut v___y_4633_: *mut leanh::LeanObject,
    mut v___y_4634_: *mut leanh::LeanObject,
    mut v___y_4635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4637_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___redArg(v_mod_4625_, v_isMeta_4626_, v_hint_4627_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_);
    return v___x_4637_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3___boxed(
    mut v_mod_4638_: *mut leanh::LeanObject,
    mut v_isMeta_4639_: *mut leanh::LeanObject,
    mut v_hint_4640_: *mut leanh::LeanObject,
    mut v___y_4641_: *mut leanh::LeanObject,
    mut v___y_4642_: *mut leanh::LeanObject,
    mut v___y_4643_: *mut leanh::LeanObject,
    mut v___y_4644_: *mut leanh::LeanObject,
    mut v___y_4645_: *mut leanh::LeanObject,
    mut v___y_4646_: *mut leanh::LeanObject,
    mut v___y_4647_: *mut leanh::LeanObject,
    mut v___y_4648_: *mut leanh::LeanObject,
    mut v___y_4649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isMeta_boxed_4650_: u8 = 0;
    let mut v_res_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_4650_ = (leanh::lean_unbox(v_isMeta_4639_) as u8);
    v_res_4651_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3(v_mod_4638_, v_isMeta_boxed_4650_, v_hint_4640_, v___y_4641_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
    leanh::lean_dec(v___y_4648_);
    leanh::lean_dec_ref(v___y_4647_);
    leanh::lean_dec(v___y_4646_);
    leanh::lean_dec_ref(v___y_4645_);
    leanh::lean_dec(v___y_4644_);
    leanh::lean_dec_ref(v___y_4643_);
    leanh::lean_dec(v___y_4642_);
    leanh::lean_dec_ref(v___y_4641_);
    return v_res_4651_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5(
    mut v_00_u03b2_4652_: *mut leanh::LeanObject,
    mut v_m_4653_: *mut leanh::LeanObject,
    mut v_a_4654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4655_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___redArg(v_m_4653_, v_a_4654_);
    return v___x_4655_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5___boxed(
    mut v_00_u03b2_4656_: *mut leanh::LeanObject,
    mut v_m_4657_: *mut leanh::LeanObject,
    mut v_a_4658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4659_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5(v_00_u03b2_4656_, v_m_4657_, v_a_4658_);
    leanh::lean_dec(v_a_4658_);
    leanh::lean_dec_ref(v_m_4657_);
    return v_res_4659_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12(
    mut v_00_u03b2_4660_: *mut leanh::LeanObject,
    mut v_x_4661_: *mut leanh::LeanObject,
    mut v_x_4662_: usize,
    mut v_x_4663_: usize,
    mut v_x_4664_: *mut leanh::LeanObject,
    mut v_x_4665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4666_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___redArg(v_x_4661_, v_x_4662_, v_x_4663_, v_x_4664_, v_x_4665_);
    return v___x_4666_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12___boxed(
    mut v_00_u03b2_4667_: *mut leanh::LeanObject,
    mut v_x_4668_: *mut leanh::LeanObject,
    mut v_x_4669_: *mut leanh::LeanObject,
    mut v_x_4670_: *mut leanh::LeanObject,
    mut v_x_4671_: *mut leanh::LeanObject,
    mut v_x_4672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_19703__boxed_4673_: usize = 0;
    let mut v_x_19704__boxed_4674_: usize = 0;
    let mut v_res_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_19703__boxed_4673_ = leanh::lean_unbox_usize(v_x_4669_);
    leanh::lean_dec(v_x_4669_);
    v_x_19704__boxed_4674_ = leanh::lean_unbox_usize(v_x_4670_);
    leanh::lean_dec(v_x_4670_);
    v_res_4675_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12(v_00_u03b2_4667_, v_x_4668_, v_x_19703__boxed_4673_, v_x_19704__boxed_4674_, v_x_4671_, v_x_4672_);
    return v_res_4675_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6(
    mut v_00_u03b2_4676_: *mut leanh::LeanObject,
    mut v_x_4677_: *mut leanh::LeanObject,
    mut v_x_4678_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4679_: u8 = 0;
    v___x_4679_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___redArg(v_x_4677_, v_x_4678_);
    return v___x_4679_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6___boxed(
    mut v_00_u03b2_4680_: *mut leanh::LeanObject,
    mut v_x_4681_: *mut leanh::LeanObject,
    mut v_x_4682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4683_: u8 = 0;
    let mut v_r_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4683_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6(v_00_u03b2_4680_, v_x_4681_, v_x_4682_);
    leanh::lean_dec_ref(v_x_4682_);
    leanh::lean_dec_ref(v_x_4681_);
    v_r_4684_ = leanh::lean_box((v_res_4683_) as usize);
    return v_r_4684_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9(
    mut v_00_u03b2_4685_: *mut leanh::LeanObject,
    mut v_a_4686_: *mut leanh::LeanObject,
    mut v_x_4687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4688_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9___redArg(v_a_4686_, v_x_4687_);
    return v___x_4688_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9___boxed(
    mut v_00_u03b2_4689_: *mut leanh::LeanObject,
    mut v_a_4690_: *mut leanh::LeanObject,
    mut v_x_4691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4692_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__5_spec__9(v_00_u03b2_4689_, v_a_4690_, v_x_4691_);
    leanh::lean_dec(v_x_4691_);
    leanh::lean_dec(v_a_4690_);
    return v_res_4692_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15(
    mut v_00_u03b2_4693_: *mut leanh::LeanObject,
    mut v_n_4694_: *mut leanh::LeanObject,
    mut v_k_4695_: *mut leanh::LeanObject,
    mut v_v_4696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4697_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15___redArg(v_n_4694_, v_k_4695_, v_v_4696_);
    return v___x_4697_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16(
    mut v_00_u03b2_4698_: *mut leanh::LeanObject,
    mut v_depth_4699_: usize,
    mut v_keys_4700_: *mut leanh::LeanObject,
    mut v_vals_4701_: *mut leanh::LeanObject,
    mut v_heq_4702_: *mut leanh::LeanObject,
    mut v_i_4703_: *mut leanh::LeanObject,
    mut v_entries_4704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4705_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___redArg(v_depth_4699_, v_keys_4700_, v_vals_4701_, v_i_4703_, v_entries_4704_);
    return v___x_4705_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16___boxed(
    mut v_00_u03b2_4706_: *mut leanh::LeanObject,
    mut v_depth_4707_: *mut leanh::LeanObject,
    mut v_keys_4708_: *mut leanh::LeanObject,
    mut v_vals_4709_: *mut leanh::LeanObject,
    mut v_heq_4710_: *mut leanh::LeanObject,
    mut v_i_4711_: *mut leanh::LeanObject,
    mut v_entries_4712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_4713_: usize = 0;
    let mut v_res_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4713_ = leanh::lean_unbox_usize(v_depth_4707_);
    leanh::lean_dec(v_depth_4707_);
    v_res_4714_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__16(v_00_u03b2_4706_, v_depth_boxed_4713_, v_keys_4708_, v_vals_4709_, v_heq_4710_, v_i_4711_, v_entries_4712_);
    leanh::lean_dec_ref(v_vals_4709_);
    leanh::lean_dec_ref(v_keys_4708_);
    return v_res_4714_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11(
    mut v_00_u03b2_4715_: *mut leanh::LeanObject,
    mut v_x_4716_: *mut leanh::LeanObject,
    mut v_x_4717_: usize,
    mut v_x_4718_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4719_: u8 = 0;
    v___x_4719_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___redArg(v_x_4716_, v_x_4717_, v_x_4718_);
    return v___x_4719_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11___boxed(
    mut v_00_u03b2_4720_: *mut leanh::LeanObject,
    mut v_x_4721_: *mut leanh::LeanObject,
    mut v_x_4722_: *mut leanh::LeanObject,
    mut v_x_4723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_19737__boxed_4724_: usize = 0;
    let mut v_res_4725_: u8 = 0;
    let mut v_r_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_19737__boxed_4724_ = leanh::lean_unbox_usize(v_x_4722_);
    leanh::lean_dec(v_x_4722_);
    v_res_4725_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11(v_00_u03b2_4720_, v_x_4721_, v_x_19737__boxed_4724_, v_x_4723_);
    leanh::lean_dec_ref(v_x_4723_);
    leanh::lean_dec_ref(v_x_4721_);
    v_r_4726_ = leanh::lean_box((v_res_4725_) as usize);
    return v_r_4726_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15_spec__17(
    mut v_00_u03b2_4727_: *mut leanh::LeanObject,
    mut v_x_4728_: *mut leanh::LeanObject,
    mut v_x_4729_: *mut leanh::LeanObject,
    mut v_x_4730_: *mut leanh::LeanObject,
    mut v_x_4731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4732_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__1_spec__7_spec__12_spec__15_spec__17___redArg(v_x_4728_, v_x_4729_, v_x_4730_, v_x_4731_);
    return v___x_4732_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15(
    mut v_00_u03b2_4733_: *mut leanh::LeanObject,
    mut v_keys_4734_: *mut leanh::LeanObject,
    mut v_vals_4735_: *mut leanh::LeanObject,
    mut v_heq_4736_: *mut leanh::LeanObject,
    mut v_i_4737_: *mut leanh::LeanObject,
    mut v_k_4738_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4739_: u8 = 0;
    v___x_4739_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___redArg(v_keys_4734_, v_i_4737_, v_k_4738_);
    return v___x_4739_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15___boxed(
    mut v_00_u03b2_4740_: *mut leanh::LeanObject,
    mut v_keys_4741_: *mut leanh::LeanObject,
    mut v_vals_4742_: *mut leanh::LeanObject,
    mut v_heq_4743_: *mut leanh::LeanObject,
    mut v_i_4744_: *mut leanh::LeanObject,
    mut v_k_4745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4746_: u8 = 0;
    let mut v_r_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4746_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_Do_ProofMode_elabMRefine_spec__0_spec__1_spec__3_spec__6_spec__11_spec__15(v_00_u03b2_4740_, v_keys_4741_, v_vals_4742_, v_heq_4743_, v_i_4744_, v_k_4745_);
    leanh::lean_dec_ref(v_k_4745_);
    leanh::lean_dec_ref(v_vals_4742_);
    leanh::lean_dec_ref(v_keys_4741_);
    v_r_4747_ = leanh::lean_box((v_res_4746_) as usize);
    return v_r_4747_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1()
-> *mut leanh::LeanObject {
    let mut v___x_4759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4759_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_4760_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3;
    v___x_4761_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___closed__3;
    v___x_4762_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_4763_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4759_,
        v___x_4760_,
        v___x_4761_,
        v___x_4762_,
    );
    return v___x_4763_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1___boxed(
    mut v_a_4764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4765_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1();
    return v_res_4765_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg(
    mut v_as_4784_: *mut leanh::LeanObject,
    mut v_i_4785_: usize,
    mut v_stop_4786_: usize,
    mut v_b_4787_: *mut leanh::LeanObject,
    mut v___y_4788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4790_: u8 = 0;
    let mut v_ref_4791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: usize = 0;
    let mut v___x_4794_: usize = 0;
    let mut v___x_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4790_ = lean_usize_dec_eq(v_i_4785_, v_stop_4786_);
                if v___x_4790_ == 0 {
                    v_ref_4791_ = leanh::lean_ctor_get(v___y_4788_, 5);
                    v___x_4792_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__0;
                    v___x_4793_ = 1usize;
                    v___x_4794_ = lean_usize_sub(v_i_4785_, v___x_4793_);
                    v___x_4795_ = lean_array_uget_borrowed(v_as_4784_, v___x_4794_);
                    v___x_4796_ = l_Lean_SourceInfo_fromRef(v_ref_4791_, v___x_4790_);
                    v___x_4797_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2;
                    v___x_4798_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__3;
                    leanh::lean_inc_n(v___x_4796_, 5);
                    v___x_4799_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4799_, 0, v___x_4796_);
                    leanh::lean_ctor_set(v___x_4799_, 1, v___x_4798_);
                    v___x_4800_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5;
                    v___x_4801_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__7;
                    v___x_4802_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4802_, 0, v___x_4796_);
                    leanh::lean_ctor_set(v___x_4802_, 1, v___x_4792_);
                    leanh::lean_inc(v___x_4795_);
                    v___x_4803_ = l_Lean_Syntax_node3(
                        v___x_4796_,
                        v___x_4801_,
                        v___x_4795_,
                        v___x_4802_,
                        v_b_4787_,
                    );
                    v___x_4804_ = l_Lean_Syntax_node1(v___x_4796_, v___x_4800_, v___x_4803_);
                    v___x_4805_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__8;
                    v___x_4806_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4806_, 0, v___x_4796_);
                    leanh::lean_ctor_set(v___x_4806_, 1, v___x_4805_);
                    v___x_4807_ = l_Lean_Syntax_node3(
                        v___x_4796_,
                        v___x_4797_,
                        v___x_4799_,
                        v___x_4804_,
                        v___x_4806_,
                    );
                    v_i_4785_ = v___x_4794_;
                    v_b_4787_ = v___x_4807_;
                    state = 0;
                    continue;
                } else {
                    v___x_4809_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4809_, 0, v_b_4787_);
                    return v___x_4809_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___boxed(
    mut v_as_4810_: *mut leanh::LeanObject,
    mut v_i_4811_: *mut leanh::LeanObject,
    mut v_stop_4812_: *mut leanh::LeanObject,
    mut v_b_4813_: *mut leanh::LeanObject,
    mut v___y_4814_: *mut leanh::LeanObject,
    mut v___y_4815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4816_: usize = 0;
    let mut v_stop_boxed_4817_: usize = 0;
    let mut v_res_4818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4816_ = leanh::lean_unbox_usize(v_i_4811_);
    leanh::lean_dec(v_i_4811_);
    v_stop_boxed_4817_ = leanh::lean_unbox_usize(v_stop_4812_);
    leanh::lean_dec(v_stop_4812_);
    v_res_4818_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg(v_as_4810_, v_i_boxed_4816_, v_stop_boxed_4817_, v_b_4813_, v___y_4814_);
    leanh::lean_dec_ref(v___y_4814_);
    leanh::lean_dec_ref(v_as_4810_);
    return v_res_4818_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1(
    mut v_as_4819_: *mut leanh::LeanObject,
    mut v_i_4820_: usize,
    mut v_stop_4821_: usize,
    mut v_b_4822_: *mut leanh::LeanObject,
    mut v___y_4823_: *mut leanh::LeanObject,
    mut v___y_4824_: *mut leanh::LeanObject,
    mut v___y_4825_: *mut leanh::LeanObject,
    mut v___y_4826_: *mut leanh::LeanObject,
    mut v___y_4827_: *mut leanh::LeanObject,
    mut v___y_4828_: *mut leanh::LeanObject,
    mut v___y_4829_: *mut leanh::LeanObject,
    mut v___y_4830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4832_: u8 = 0;
    v___x_4832_ = lean_usize_dec_eq(v_i_4820_, v_stop_4821_);
    if v___x_4832_ == 0 {
        let mut v_ref_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4834_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4835_: usize = 0;
        let mut v___x_4836_: usize = 0;
        let mut v___x_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4838_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4839_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4840_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4842_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4845_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4846_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4847_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4849_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_ref_4833_ = leanh::lean_ctor_get(v___y_4829_, 5);
        v___x_4834_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__0;
        v___x_4835_ = 1usize;
        v___x_4836_ = lean_usize_sub(v_i_4820_, v___x_4835_);
        v___x_4837_ = lean_array_uget_borrowed(v_as_4819_, v___x_4836_);
        v___x_4838_ = l_Lean_SourceInfo_fromRef(v_ref_4833_, v___x_4832_);
        v___x_4839_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__2;
        v___x_4840_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__3;
        leanh::lean_inc_n(v___x_4838_, 5);
        v___x_4841_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4841_, 0, v___x_4838_);
        leanh::lean_ctor_set(v___x_4841_, 1, v___x_4840_);
        v___x_4842_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__5;
        v___x_4843_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__7;
        v___x_4844_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4844_, 0, v___x_4838_);
        leanh::lean_ctor_set(v___x_4844_, 1, v___x_4834_);
        leanh::lean_inc(v___x_4837_);
        v___x_4845_ = l_Lean_Syntax_node3(
            v___x_4838_,
            v___x_4843_,
            v___x_4837_,
            v___x_4844_,
            v_b_4822_,
        );
        v___x_4846_ = l_Lean_Syntax_node1(v___x_4838_, v___x_4842_, v___x_4845_);
        v___x_4847_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__8;
        v___x_4848_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4848_, 0, v___x_4838_);
        leanh::lean_ctor_set(v___x_4848_, 1, v___x_4847_);
        v___x_4849_ = l_Lean_Syntax_node3(
            v___x_4838_,
            v___x_4839_,
            v___x_4841_,
            v___x_4846_,
            v___x_4848_,
        );
        v___x_4850_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg(v_as_4819_, v___x_4836_, v_stop_4821_, v___x_4849_, v___y_4829_);
        return v___x_4850_;
    } else {
        let mut v___x_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4851_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4851_, 0, v_b_4822_);
        return v___x_4851_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1___boxed(
    mut v_as_4852_: *mut leanh::LeanObject,
    mut v_i_4853_: *mut leanh::LeanObject,
    mut v_stop_4854_: *mut leanh::LeanObject,
    mut v_b_4855_: *mut leanh::LeanObject,
    mut v___y_4856_: *mut leanh::LeanObject,
    mut v___y_4857_: *mut leanh::LeanObject,
    mut v___y_4858_: *mut leanh::LeanObject,
    mut v___y_4859_: *mut leanh::LeanObject,
    mut v___y_4860_: *mut leanh::LeanObject,
    mut v___y_4861_: *mut leanh::LeanObject,
    mut v___y_4862_: *mut leanh::LeanObject,
    mut v___y_4863_: *mut leanh::LeanObject,
    mut v___y_4864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4865_: usize = 0;
    let mut v_stop_boxed_4866_: usize = 0;
    let mut v_res_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4865_ = leanh::lean_unbox_usize(v_i_4853_);
    leanh::lean_dec(v_i_4853_);
    v_stop_boxed_4866_ = leanh::lean_unbox_usize(v_stop_4854_);
    leanh::lean_dec(v_stop_4854_);
    v_res_4867_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1(v_as_4852_, v_i_boxed_4865_, v_stop_boxed_4866_, v_b_4855_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_);
    leanh::lean_dec(v___y_4863_);
    leanh::lean_dec_ref(v___y_4862_);
    leanh::lean_dec(v___y_4861_);
    leanh::lean_dec_ref(v___y_4860_);
    leanh::lean_dec(v___y_4859_);
    leanh::lean_dec_ref(v___y_4858_);
    leanh::lean_dec(v___y_4857_);
    leanh::lean_dec_ref(v___y_4856_);
    leanh::lean_dec_ref(v_as_4852_);
    return v_res_4867_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg(
    mut v_sz_4876_: usize,
    mut v_i_4877_: usize,
    mut v_bs_4878_: *mut leanh::LeanObject,
    mut v___y_4879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4881_: u8 = 0;
    let mut v___x_4882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: u8 = 0;
    let mut v___x_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: usize = 0;
    let mut v___x_4896_: usize = 0;
    let mut v___x_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4881_ = lean_usize_dec_lt(v_i_4877_, v_sz_4876_);
                if v___x_4881_ == 0 {
                    v___x_4882_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4882_, 0, v_bs_4878_);
                    return v___x_4882_;
                } else {
                    v_ref_4883_ = leanh::lean_ctor_get(v___y_4879_, 5);
                    v_v_4884_ = lean_array_uget(v_bs_4878_, v_i_4877_);
                    v___x_4885_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4886_ = lean_array_uset(v_bs_4878_, v_i_4877_, v___x_4885_);
                    v___x_4887_ = 0;
                    v___x_4888_ = l_Lean_SourceInfo_fromRef(v_ref_4883_, v___x_4887_);
                    v___x_4889_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__1;
                    v___x_4890_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__2;
                    leanh::lean_inc_n(v___x_4888_, 2);
                    v___x_4891_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4891_, 0, v___x_4888_);
                    leanh::lean_ctor_set(v___x_4891_, 1, v___x_4890_);
                    v___x_4892_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___closed__3;
                    v___x_4893_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4893_, 0, v___x_4888_);
                    leanh::lean_ctor_set(v___x_4893_, 1, v___x_4892_);
                    v___x_4894_ = l_Lean_Syntax_node3(
                        v___x_4888_,
                        v___x_4889_,
                        v___x_4891_,
                        v_v_4884_,
                        v___x_4893_,
                    );
                    v___x_4895_ = 1usize;
                    v___x_4896_ = lean_usize_add(v_i_4877_, v___x_4895_);
                    v___x_4897_ = lean_array_uset(v_bs_x27_4886_, v_i_4877_, v___x_4894_);
                    v_i_4877_ = v___x_4896_;
                    v_bs_4878_ = v___x_4897_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg___boxed(
    mut v_sz_4899_: *mut leanh::LeanObject,
    mut v_i_4900_: *mut leanh::LeanObject,
    mut v_bs_4901_: *mut leanh::LeanObject,
    mut v___y_4902_: *mut leanh::LeanObject,
    mut v___y_4903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4904_: usize = 0;
    let mut v_i_boxed_4905_: usize = 0;
    let mut v_res_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4904_ = leanh::lean_unbox_usize(v_sz_4899_);
    leanh::lean_dec(v_sz_4899_);
    v_i_boxed_4905_ = leanh::lean_unbox_usize(v_i_4900_);
    leanh::lean_dec(v_i_4900_);
    v_res_4906_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg(v_sz_boxed_4904_, v_i_boxed_4905_, v_bs_4901_, v___y_4902_);
    leanh::lean_dec_ref(v___y_4902_);
    return v_res_4906_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMExists(
    mut v_x_4962_: *mut leanh::LeanObject,
    mut v_a_4963_: *mut leanh::LeanObject,
    mut v_a_4964_: *mut leanh::LeanObject,
    mut v_a_4965_: *mut leanh::LeanObject,
    mut v_a_4966_: *mut leanh::LeanObject,
    mut v_a_4967_: *mut leanh::LeanObject,
    mut v_a_4968_: *mut leanh::LeanObject,
    mut v_a_4969_: *mut leanh::LeanObject,
    mut v_a_4970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: u8 = 0;
    let mut v___x_4974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4979_: usize = 0;
    let mut v___x_4980_: usize = 0;
    let mut v___x_4981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: u8 = 0;
    let mut v___x_4986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: u8 = 0;
    let mut v___x_5031_: usize = 0;
    let mut v___x_5032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5037_: u8 = 0;
    let mut v___x_5039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5041_: u8 = 0;
    let mut v_a_5042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5045_: u8 = 0;
    let mut v___x_5047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5049_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4972_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1;
                leanh::lean_inc(v_x_4962_);
                v___x_4973_ = l_Lean_Syntax_isOfKind(v_x_4962_, v___x_4972_);
                if v___x_4973_ == 0 {
                    leanh::lean_dec(v_x_4962_);
                    v___x_4974_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_mRefineCore_spec__0___redArg();
                    return v___x_4974_;
                } else {
                    v___x_4975_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4976_ = l_Lean_Syntax_getArg(v_x_4962_, v___x_4975_);
                    leanh::lean_dec(v_x_4962_);
                    v_args_4977_ = l_Lean_Syntax_getArgs(v___x_4976_);
                    leanh::lean_dec(v___x_4976_);
                    v___x_4978_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_args_4977_);
                    leanh::lean_dec_ref(v_args_4977_);
                    v_sz_4979_ = lean_array_size(v___x_4978_);
                    v___x_4980_ = 0usize;
                    v___x_4981_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg(v_sz_4979_, v___x_4980_, v___x_4978_, v_a_4969_);
                    if leanh::lean_obj_tag(v___x_4981_) == 0 {
                        v_a_4982_ = leanh::lean_ctor_get(v___x_4981_, 0);
                        leanh::lean_inc(v_a_4982_);
                        leanh::lean_dec_ref_known(v___x_4981_, 1);
                        v_ref_4983_ = leanh::lean_ctor_get(v_a_4969_, 5);
                        v___x_4984_ = leanh::lean_unsigned_to_nat(0);
                        v___x_4985_ = 0;
                        v___x_4986_ = l_Lean_SourceInfo_fromRef(v_ref_4983_, v___x_4985_);
                        v___x_5019_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__17;
                        v___x_5020_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__18;
                        leanh::lean_inc_n(v___x_4986_, 5);
                        v___x_5021_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5021_, 0, v___x_4986_);
                        leanh::lean_ctor_set(v___x_5021_, 1, v___x_5020_);
                        v___x_5022_ = l_Lean_Elab_Tactic_Do_ProofMode_patAsTerm___closed__2;
                        v___x_5023_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__21;
                        v___x_5024_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__22;
                        v___x_5025_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5025_, 0, v___x_4986_);
                        leanh::lean_ctor_set(v___x_5025_, 1, v___x_5024_);
                        v___x_5026_ = l_Lean_Syntax_node1(v___x_4986_, v___x_5023_, v___x_5025_);
                        v___x_5027_ = l_Lean_Syntax_node1(v___x_4986_, v___x_5022_, v___x_5026_);
                        v___x_5028_ =
                            l_Lean_Syntax_node2(v___x_4986_, v___x_5019_, v___x_5021_, v___x_5027_);
                        v___x_5029_ = lean_array_get_size(v_a_4982_);
                        v___x_5030_ = lean_nat_dec_lt(v___x_4984_, v___x_5029_);
                        if v___x_5030_ == 0 {
                            leanh::lean_dec(v_a_4982_);
                            v_a_4988_ = v___x_5028_;
                            state = 1;
                            continue;
                        } else {
                            v___x_5031_ = lean_usize_of_nat(v___x_5029_);
                            v___x_5032_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1(v_a_4982_, v___x_5031_, v___x_4980_, v___x_5028_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_);
                            leanh::lean_dec(v_a_4982_);
                            if leanh::lean_obj_tag(v___x_5032_) == 0 {
                                v_a_5033_ = leanh::lean_ctor_get(v___x_5032_, 0);
                                leanh::lean_inc(v_a_5033_);
                                leanh::lean_dec_ref_known(v___x_5032_, 1);
                                v_a_4988_ = v_a_5033_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_4986_);
                                v_a_5034_ = leanh::lean_ctor_get(v___x_5032_, 0);
                                v_isSharedCheck_5041_ =
                                    (!leanh::lean_is_exclusive(v___x_5032_)) as u8;
                                if v_isSharedCheck_5041_ == 0 {
                                    v___x_5036_ = v___x_5032_;
                                    v_isShared_5037_ = v_isSharedCheck_5041_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5034_);
                                    leanh::lean_dec(v___x_5032_);
                                    v___x_5036_ = leanh::lean_box(0);
                                    v_isShared_5037_ = v_isSharedCheck_5041_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v_a_5042_ = leanh::lean_ctor_get(v___x_4981_, 0);
                        v_isSharedCheck_5049_ =
                            (!leanh::lean_is_exclusive(v___x_4981_)) as u8;
                        if v_isSharedCheck_5049_ == 0 {
                            v___x_5044_ = v___x_4981_;
                            v_isShared_5045_ = v_isSharedCheck_5049_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5042_);
                            leanh::lean_dec(v___x_4981_);
                            v___x_5044_ = leanh::lean_box(0);
                            v_isShared_5045_ = v_isSharedCheck_5049_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4989_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__3;
                v___x_4990_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__4;
                leanh::lean_inc_n(v___x_4986_, 15);
                v___x_4991_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4991_, 0, v___x_4986_);
                leanh::lean_ctor_set(v___x_4991_, 1, v___x_4990_);
                v___x_4992_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__6;
                v___x_4993_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__8;
                v___x_4994_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg___closed__7;
                v___x_4995_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__2;
                v___x_4996_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRefine___closed__3;
                v___x_4997_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4997_, 0, v___x_4986_);
                leanh::lean_ctor_set(v___x_4997_, 1, v___x_4995_);
                v___x_4998_ = l_Lean_Syntax_node2(v___x_4986_, v___x_4996_, v___x_4997_, v_a_4988_);
                v___x_4999_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__9;
                v___x_5000_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5000_, 0, v___x_4986_);
                leanh::lean_ctor_set(v___x_5000_, 1, v___x_4999_);
                v___x_5001_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__11;
                v___x_5002_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__12;
                v___x_5003_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5003_, 0, v___x_4986_);
                leanh::lean_ctor_set(v___x_5003_, 1, v___x_5002_);
                v___x_5004_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__13;
                v___x_5005_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__14;
                v___x_5006_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5006_, 0, v___x_4986_);
                leanh::lean_ctor_set(v___x_5006_, 1, v___x_5004_);
                v___x_5007_ = l_Lean_Syntax_node1(v___x_4986_, v___x_5005_, v___x_5006_);
                v___x_5008_ = l_Lean_Syntax_node1(v___x_4986_, v___x_4994_, v___x_5007_);
                v___x_5009_ = l_Lean_Syntax_node1(v___x_4986_, v___x_4993_, v___x_5008_);
                v___x_5010_ = l_Lean_Syntax_node1(v___x_4986_, v___x_4992_, v___x_5009_);
                v___x_5011_ =
                    l_Lean_Syntax_node2(v___x_4986_, v___x_5001_, v___x_5003_, v___x_5010_);
                v___x_5012_ = l_Lean_Syntax_node3(
                    v___x_4986_,
                    v___x_4994_,
                    v___x_4998_,
                    v___x_5000_,
                    v___x_5011_,
                );
                v___x_5013_ = l_Lean_Syntax_node1(v___x_4986_, v___x_4993_, v___x_5012_);
                v___x_5014_ = l_Lean_Syntax_node1(v___x_4986_, v___x_4992_, v___x_5013_);
                v___x_5015_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__15;
                v___x_5016_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5016_, 0, v___x_4986_);
                leanh::lean_ctor_set(v___x_5016_, 1, v___x_5015_);
                v___x_5017_ = l_Lean_Syntax_node3(
                    v___x_4986_,
                    v___x_4989_,
                    v___x_4991_,
                    v___x_5014_,
                    v___x_5016_,
                );
                v___x_5018_ = l_Lean_Elab_Tactic_evalTactic(
                    v___x_5017_,
                    v_a_4963_,
                    v_a_4964_,
                    v_a_4965_,
                    v_a_4966_,
                    v_a_4967_,
                    v_a_4968_,
                    v_a_4969_,
                    v_a_4970_,
                );
                return v___x_5018_;
            }
            2 => {
                if v_isShared_5037_ == 0 {
                    v___x_5039_ = v___x_5036_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5040_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5040_, 0, v_a_5034_);
                    v___x_5039_ = v_reuseFailAlloc_5040_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5039_;
            }
            4 => {
                if v_isShared_5045_ == 0 {
                    v___x_5047_ = v___x_5044_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5048_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5048_, 0, v_a_5042_);
                    v___x_5047_ = v_reuseFailAlloc_5048_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5047_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___boxed(
    mut v_x_5050_: *mut leanh::LeanObject,
    mut v_a_5051_: *mut leanh::LeanObject,
    mut v_a_5052_: *mut leanh::LeanObject,
    mut v_a_5053_: *mut leanh::LeanObject,
    mut v_a_5054_: *mut leanh::LeanObject,
    mut v_a_5055_: *mut leanh::LeanObject,
    mut v_a_5056_: *mut leanh::LeanObject,
    mut v_a_5057_: *mut leanh::LeanObject,
    mut v_a_5058_: *mut leanh::LeanObject,
    mut v_a_5059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5060_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists(
        v_x_5050_, v_a_5051_, v_a_5052_, v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_, v_a_5057_,
        v_a_5058_,
    );
    leanh::lean_dec(v_a_5058_);
    leanh::lean_dec_ref(v_a_5057_);
    leanh::lean_dec(v_a_5056_);
    leanh::lean_dec_ref(v_a_5055_);
    leanh::lean_dec(v_a_5054_);
    leanh::lean_dec_ref(v_a_5053_);
    leanh::lean_dec(v_a_5052_);
    leanh::lean_dec_ref(v_a_5051_);
    return v_res_5060_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0(
    mut v_sz_5061_: usize,
    mut v_i_5062_: usize,
    mut v_bs_5063_: *mut leanh::LeanObject,
    mut v___y_5064_: *mut leanh::LeanObject,
    mut v___y_5065_: *mut leanh::LeanObject,
    mut v___y_5066_: *mut leanh::LeanObject,
    mut v___y_5067_: *mut leanh::LeanObject,
    mut v___y_5068_: *mut leanh::LeanObject,
    mut v___y_5069_: *mut leanh::LeanObject,
    mut v___y_5070_: *mut leanh::LeanObject,
    mut v___y_5071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5073_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___redArg(v_sz_5061_, v_i_5062_, v_bs_5063_, v___y_5070_);
    return v___x_5073_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0___boxed(
    mut v_sz_5074_: *mut leanh::LeanObject,
    mut v_i_5075_: *mut leanh::LeanObject,
    mut v_bs_5076_: *mut leanh::LeanObject,
    mut v___y_5077_: *mut leanh::LeanObject,
    mut v___y_5078_: *mut leanh::LeanObject,
    mut v___y_5079_: *mut leanh::LeanObject,
    mut v___y_5080_: *mut leanh::LeanObject,
    mut v___y_5081_: *mut leanh::LeanObject,
    mut v___y_5082_: *mut leanh::LeanObject,
    mut v___y_5083_: *mut leanh::LeanObject,
    mut v___y_5084_: *mut leanh::LeanObject,
    mut v___y_5085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5086_: usize = 0;
    let mut v_i_boxed_5087_: usize = 0;
    let mut v_res_5088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5086_ = leanh::lean_unbox_usize(v_sz_5074_);
    leanh::lean_dec(v_sz_5074_);
    v_i_boxed_5087_ = leanh::lean_unbox_usize(v_i_5075_);
    leanh::lean_dec(v_i_5075_);
    v_res_5088_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__0(v_sz_boxed_5086_, v_i_boxed_5087_, v_bs_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_);
    leanh::lean_dec(v___y_5084_);
    leanh::lean_dec_ref(v___y_5083_);
    leanh::lean_dec(v___y_5082_);
    leanh::lean_dec_ref(v___y_5081_);
    leanh::lean_dec(v___y_5080_);
    leanh::lean_dec_ref(v___y_5079_);
    leanh::lean_dec(v___y_5078_);
    leanh::lean_dec_ref(v___y_5077_);
    return v_res_5088_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1(
    mut v_as_5089_: *mut leanh::LeanObject,
    mut v_i_5090_: usize,
    mut v_stop_5091_: usize,
    mut v_b_5092_: *mut leanh::LeanObject,
    mut v___y_5093_: *mut leanh::LeanObject,
    mut v___y_5094_: *mut leanh::LeanObject,
    mut v___y_5095_: *mut leanh::LeanObject,
    mut v___y_5096_: *mut leanh::LeanObject,
    mut v___y_5097_: *mut leanh::LeanObject,
    mut v___y_5098_: *mut leanh::LeanObject,
    mut v___y_5099_: *mut leanh::LeanObject,
    mut v___y_5100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5102_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___redArg(v_as_5089_, v_i_5090_, v_stop_5091_, v_b_5092_, v___y_5099_);
    return v___x_5102_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1___boxed(
    mut v_as_5103_: *mut leanh::LeanObject,
    mut v_i_5104_: *mut leanh::LeanObject,
    mut v_stop_5105_: *mut leanh::LeanObject,
    mut v_b_5106_: *mut leanh::LeanObject,
    mut v___y_5107_: *mut leanh::LeanObject,
    mut v___y_5108_: *mut leanh::LeanObject,
    mut v___y_5109_: *mut leanh::LeanObject,
    mut v___y_5110_: *mut leanh::LeanObject,
    mut v___y_5111_: *mut leanh::LeanObject,
    mut v___y_5112_: *mut leanh::LeanObject,
    mut v___y_5113_: *mut leanh::LeanObject,
    mut v___y_5114_: *mut leanh::LeanObject,
    mut v___y_5115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5116_: usize = 0;
    let mut v_stop_boxed_5117_: usize = 0;
    let mut v_res_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5116_ = leanh::lean_unbox_usize(v_i_5104_);
    leanh::lean_dec(v_i_5104_);
    v_stop_boxed_5117_ = leanh::lean_unbox_usize(v_stop_5105_);
    leanh::lean_dec(v_stop_5105_);
    v_res_5118_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExists_spec__1_spec__1(v_as_5103_, v_i_boxed_5116_, v_stop_boxed_5117_, v_b_5106_, v___y_5107_, v___y_5108_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_);
    leanh::lean_dec(v___y_5114_);
    leanh::lean_dec_ref(v___y_5113_);
    leanh::lean_dec(v___y_5112_);
    leanh::lean_dec_ref(v___y_5111_);
    leanh::lean_dec(v___y_5110_);
    leanh::lean_dec_ref(v___y_5109_);
    leanh::lean_dec(v___y_5108_);
    leanh::lean_dec_ref(v___y_5107_);
    leanh::lean_dec_ref(v_as_5103_);
    return v_res_5118_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1()
-> *mut leanh::LeanObject {
    let mut v___x_5128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5128_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_5129_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___closed__1;
    v___x_5130_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___closed__1;
    v___x_5131_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_elabMExists___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_5132_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_5128_,
        v___x_5129_,
        v___x_5130_,
        v___x_5131_,
    );
    return v___x_5132_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1___boxed(
    mut v_a_5133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5134_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1();
    return v_res_5134_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Refine(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMRefine___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRefine__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Refine_0__Lean_Elab_Tactic_Do_ProofMode_elabMExists___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExists__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Refine(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_ProofMode_Refine(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Assumption(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Refine(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Refine(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_ProofMode_Refine(builtin);
}